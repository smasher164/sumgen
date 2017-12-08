package main

import (
	"bytes"
	"fmt"
	"go/ast"
	"go/build"
	"go/format"
	"go/importer"
	"go/parser"
	"go/token"
	"go/types"
	"html/template"
	"io"
	"log"
	"os"
	"path/filepath"
	"strings"
	"unicode"
	"unicode/utf8"

	"github.com/nightlyone/lockfile"
	"golang.org/x/tools/go/ast/astutil"
)

type SumDef struct {
	Type *types.Interface
	Rhs  []string
}

type Func struct {
	Recv string
	Name string
	Sig  string
}

type generator struct {
	files   []*ast.File
	pkg     *types.Package
	info    *types.Info
	defs    []SumDef
	methods []Func
	imports map[string]struct{}
}

func (g *generator) parseAndTypeCheck(dir string) error {
	fset := token.NewFileSet()
	files, err := parseInDir(dir, fset)
	if err != nil {
		return err
	}

	config := types.Config{Importer: importer.Default(), FakeImportC: true}
	info := &types.Info{
		Types: make(map[ast.Expr]types.TypeAndValue),
		Defs:  make(map[*ast.Ident]types.Object),
		Uses:  make(map[*ast.Ident]types.Object),
	}

	pkg, err := config.Check(dir, fset, files, info)
	if err != nil {
		return err
	}
	g.files = files
	g.info = info
	g.pkg = pkg
	return nil
}

func (g *generator) parseSumDefs() error {
	var err error
	for _, file := range g.files {
		astutil.Apply(file, func(c *astutil.Cursor) bool {
			if err != nil {
				return false
			}
			gd, _ := c.Node().(*ast.GenDecl)
			if gd == nil {
				return true
			}
			for _, spec := range gd.Specs {
				ts, _ := spec.(*ast.TypeSpec)
				if ts == nil {
					return true
				}
				var def *SumDef
				if len(gd.Specs) == 1 {
					if def, err = scanDefs(g.info, gd.Doc, ts); err != nil {
						return false
					}
				} else {
					if def, err = scanDefs(g.info, ts.Doc, ts); err != nil {
						return false
					}
				}
				if def != nil {
					g.defs = append(g.defs, *def)
				}
			}
			return true
		}, nil)
	}
	return err
}

func (g *generator) genMissingMethods() error {
	for _, def := range g.defs {
		for _, rhstype := range def.Rhs {
			var addressable bool
			if rhstype[0] == '*' {
				addressable = true
				rhstype = rhstype[1:]
			}
			rtyp := g.pkg.Scope().Lookup(rhstype).Type()
			mds, err := g.missingMethods(g.pkg, addressable, rtyp, def.Type)
			if err != nil {
				return err
			}
			g.methods = append(g.methods, mds...)
		}
	}
	return nil
}

func parseInDir(dir string, fset *token.FileSet) ([]*ast.File, error) {
	pkg, err := build.Default.ImportDir(dir, 0)
	if err != nil {
		return nil, err
	}
	var names []string
	// should we worry about .s files?
	names = append(names, pkg.GoFiles...)
	names = append(names, pkg.CgoFiles...)

	var files []*ast.File
	for _, name := range names {
		if !strings.HasSuffix(name, ".go") {
			continue
		}
		fname := filepath.Join(dir, name)
		file, err := parser.ParseFile(fset, fname, nil, parser.ParseComments)
		if err != nil {
			return nil, err
		}
		files = append(files, file)
	}
	if len(files) == 0 {
		return nil, fmt.Errorf("no buildable Go files")
	}
	return files, nil
}

func isLetter(ch rune) bool {
	return 'a' <= ch && ch <= 'z' || 'A' <= ch && ch <= 'Z' || ch >= utf8.RuneSelf && unicode.IsLetter(ch)
}

func isDigit(ch rune) bool {
	return '0' <= ch && ch <= '9' || ch >= utf8.RuneSelf && unicode.IsDigit(ch)
}

func justSpaces(s string) bool {
	return strings.IndexFunc(s, func(r rune) bool {
		return !unicode.IsSpace(r)
	}) < 0
}

func ident(comment string, i int) int {
	r, _ := utf8.DecodeRuneInString(comment[i:])
	if !isLetter(r) {
		return i
	}
	for w := 0; i < len(comment); i += w {
		r, w = utf8.DecodeRuneInString(comment[i:])
		if !isLetter(r) && !isDigit(r) {
			break
		}
	}
	return i
}

// scanDefs parses the comment above an interface type definition for sum type definitions.
// A comment can have multiple definitions, and definitions can wrap to new lines.
func scanDefs(info *types.Info, doc *ast.CommentGroup, ts *ast.TypeSpec) (def *SumDef, err error) {
	const prefix = "go:generate sumgen"
	it, _ := ts.Type.(*ast.InterfaceType)
	if it == nil || doc == nil {
		return nil, nil
	}
	i, com := 0, doc.Text()
	var defs []SumDef
	for !justSpaces(com[i:]) {
		if strings.HasPrefix(com, prefix) {
			// parse single def
			com = strings.TrimLeftFunc(com[i+len(prefix):], unicode.IsSpace)
			i = 0
			// check that the token is an identifier.
			if i = ident(com, i); i == 0 {
				goto nextLine
			}
			// check that left matches the type's name
			if left := com[:i]; left != ts.Name.Name {
				goto nextLine
			}
			r, w := utf8.DecodeRuneInString(com[i:])
			for unicode.IsSpace(r) {
				i += w
				r, w = utf8.DecodeRuneInString(com[i:])
			}
			if com[i] != '=' {
				goto nextLine
			}
			i++

			var rhs []string
			// parse rhs of definition
			for {
				r, w := utf8.DecodeRuneInString(com[i:])
				for unicode.IsSpace(r) {
					i += w
					r, w = utf8.DecodeRuneInString(com[i:])
				}
				offs := i

				var ptrRec bool
				if com[i] == '*' {
					// accept a pointer receiver
					ptrRec = true
					i++
				}
				if ei := ident(com, i); ei == i {
					if ptrRec {
						return nil, fmt.Errorf("pointer receiver not followed by type name")
					}
					goto nextLine
				} else {
					i = ei
				}
				rhs = append(rhs, com[offs:i]) // ident
				r, w = utf8.DecodeRuneInString(com[i:])
				for unicode.IsSpace(r) {
					i += w
					r, w = utf8.DecodeRuneInString(com[i:])
				}
				if i < len(com) && com[i] == '|' {
					i++
				} else {
					break
				}
			}

			if len(rhs) == 0 {
				goto nextLine
			}

			// get a *types.Interface from declared type
			typ, _ := info.TypeOf(it).Underlying().(*types.Interface)
			if typ == nil {
				return nil, fmt.Errorf("could not assert that TypeOf(%T) is of type '*types.Interface'\n", it)
			}

			// survivors look like valid definitions
			defs = append(defs, SumDef{Type: typ, Rhs: rhs})
		}
	nextLine:
		// go to next line
		// TODO: refactor to do with continue and not goto
		if i = strings.IndexAny(com, "\r\n"); i >= 0 {
			com = strings.TrimLeftFunc(com[i:], unicode.IsSpace)
			i = 0
		}
	}
	return union(defs), nil
}

// union takes the union of all rhs types,
// and returns a single sum type definition.
func union(defs []SumDef) *SumDef {
	if len(defs) == 0 {
		return nil
	}
	set := make(map[string]struct{})
	var rhs []string
	for _, def := range defs {
		for _, s := range def.Rhs {
			if _, ok := set[s]; !ok {
				set[s] = struct{}{}
				rhs = append(rhs, s)
			}
		}
	}
	return &SumDef{
		Type: defs[0].Type,
		Rhs:  rhs,
	}
}

func (g *generator) sourceRepresentation(pkg *types.Package) types.Qualifier {
	if pkg == nil {
		return nil
	}
	return func(other *types.Package) string {
		if pkg == other {
			return ""
		}
		g.imports[other.Path()] = struct{}{}
		return other.Name()
	}
}

func (g *generator) missingMethods(pkg *types.Package, addressable bool, V types.Type, T *types.Interface) (methods []Func, err error) {
	tname := types.TypeString(V, types.RelativeTo(pkg))
	var buf bytes.Buffer
	n := T.NumMethods()
	for i := 0; i < n; i++ {
		m := T.Method(i)
		obj, _, _ := types.LookupFieldOrMethod(V, addressable, m.Pkg(), m.Name())
		f, _ := obj.(*types.Func)
		if obj != nil && f == nil {
			// make sure it is not a method with the same signature
			return nil, fmt.Errorf("type %s already has a field named %s", tname, obj.Name())
		}
		if f != nil {
			mSig := m.Type().(*types.Signature).String()
			fSig := f.Type().(*types.Signature).String()
			if mSig != fSig {
				return nil, fmt.Errorf("type %s already has a method named %s", tname, m.Name())
			}
		}
		if f == nil {
			buf.WriteString("func")
			types.WriteSignature(&buf, m.Type().(*types.Signature), g.sourceRepresentation(pkg))
			if addressable {
				tname = "*" + tname
			}
			methods = append(methods, Func{
				Recv: tname,
				Name: m.Name(),
				Sig:  buf.String(),
			})
			buf.Reset()
		}
	}
	return methods, nil
}

// Remove duplicate methods, avoid method overloading.
func validate(methods []Func) ([]Func, error) {
	// not sorted, so n^2 behavior might avoid multiple maps.
	// TODO: include interface name in Func def, so we can sort.
	// if two Funcs have the same Recv/Name combination
	//     if they have same sig, remove duplicate
	//     otherwise err
	for i := 0; i < len(methods); i++ {
		for j := i + 1; j < len(methods); j++ {
			if methods[i].Name == methods[j].Name &&
				methods[i].Recv == methods[j].Recv {
				if methods[i].Sig == methods[j].Sig {
					methods = append(methods[:j], methods[j+1:]...)
				} else {
					return nil, fmt.Errorf("method %s already declared for type %s", methods[j].Name, methods[j].Recv)
				}
			}
		}
	}
	return methods, nil
}

const stub = "func ({{.Recvar}} {{.Recv}}) " +
	"{{.Name}}{{.Signature}} " +
	"{ panic(\"default implementation\") }\n"

var tmpl = template.Must(template.New("test").Parse(stub))

func writeMethods(w io.Writer, methods []Func) error {
	// write methods
	for _, m := range methods {
		r, _ := utf8.DecodeRuneInString(m.Recv)
		if r == '*' {
			r, _ = utf8.DecodeRuneInString(m.Recv[1:])
		}
		recvar := string(r)
		if utf8.RuneCountInString(m.Recv) == 1 {
			recvar += m.Recv
		}
		data := struct {
			Recvar,
			Recv,
			Name,
			Signature string
		}{recvar, m.Recv, m.Name, m.Sig[4:]}
		if err := tmpl.Execute(w, data); err != nil {
			return err
		}
	}
	return nil
}

func writeHeader(w io.Writer, pkgname string) error {
	if _, err := fmt.Fprint(w, "// Code generated by \"sumgen\"; DO NOT EDIT.\n\n"); err != nil {
		return err
	}
	if _, err := fmt.Fprint(w, "\n"); err != nil {
		return err
	}
	if _, err := fmt.Fprintf(w, "package %s", pkgname); err != nil {
		return err
	}
	if _, err := fmt.Fprint(w, "\n"); err != nil {
		return err
	}
	return nil
}

func writeImports(w io.Writer, imports map[string]struct{}) error {
	if len(imports) == 0 {
		return nil
	}
	if _, err := fmt.Fprint(w, "import (\n"); err != nil {
		return err
	}
	for im := range imports {
		if _, err := fmt.Fprintf(w, "\t\"%s\"\n", im); err != nil {
			return err
		}
	}
	if _, err := fmt.Fprint(w, ")\n"); err != nil {
		return err
	}
	return nil
}

func main() {
	// configure logger
	log.SetFlags(0)
	log.SetPrefix("sumgen: ")
	var exitCode = 0
	defer func() {
		os.Exit(exitCode)
	}()
	// we want to preserve deferred function calls
	fatalln := func(v ...interface{}) {
		log.Println(v)
		exitCode = 1
	}

	// TODO: think about flags for specifying packages.
	dir, err := os.Getwd()
	if err != nil {
		fatalln(err)
		return
	}

	// create a lockfile to prevent other instances of sumgen from modifying current package
	lock, err := lockfile.New(filepath.Join(dir, "sumgen.lck"))
	if err != nil {
		fatalln("Cannot init lock. Reason: %v", err)
		return
	}
	if err = lock.TryLock(); err != nil {
		fatalln("Cannot lock %q, reason: %v", lock, err)
		return
	}
	defer lock.Unlock()

	g := &generator{imports: make(map[string]struct{})}
	// parse package in current directory
	if err := g.parseAndTypeCheck(dir); err != nil {
		fatalln(err)
		return
	}

	// Parse Sum type definitions from comments next to an interface type declaration.
	if err := g.parseSumDefs(); err != nil {
		fatalln(err)
		return
	}

	// Look up missing methods for each rhs type in the Sum type definitions.
	if err := g.genMissingMethods(); err != nil {
		fatalln(err)
		return
	}
	if g.methods, err = validate(g.methods); err != nil {
		fatalln(err)
		return
	}
	if len(g.methods) == 0 {
		return
	}

	// Write methods to a file.
	// file name is directoryname_sumgen.go. TODO: support package flags.
	fname := filepath.Base(dir) + "_sumgen.go"
	_, statErr := os.Stat(fname)
	var buf bytes.Buffer
	f, err := os.OpenFile(fname, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0644)
	if err != nil {
		fatalln(err)
		return
	}
	if os.IsNotExist(statErr) {
		// write header and package clause
		writeHeader(&buf, g.pkg.Name())
	} else {
		// read file into buffer
		if _, err := io.Copy(&buf, f); err != nil {
			log.Println(err)
		}
	}
	// write any new imports
	writeImports(&buf, g.imports)
	// append methods to buffer
	writeMethods(&buf, g.methods)
	// gofmt output
	pretty, err := format.Source(buf.Bytes())
	if err != nil {
		log.Println(err)
	}
	// output to file
	if err := f.Truncate(0); err != nil {
		log.Println(err)
	}
	if _, err := f.Seek(0, 0); err != nil {
		log.Println(err)
	}
	if _, err := f.Write(pretty); err != nil {
		log.Println(err)
	}
	if err := f.Close(); err != nil {
		fatalln(err)
		return
	}
}
