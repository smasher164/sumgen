package main

import (
	"bytes"
	"flag"
	"fmt"
	"go/format"
	"go/parser"
	"go/token"
	"go/types"
	"io/ioutil"
	"log"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"text/scanner"
	"unicode"

	"golang.org/x/tools/go/ast/astutil"
	"golang.org/x/tools/go/packages"
)

func usage() {
	fmt.Fprintf(os.Stderr, "usage: sumgen \"InterfaceName = TypeNameA, *TypeNameB, ...\"\n")
	os.Exit(2)
}

func isrhsrune(ch rune, i int) bool {
	return unicode.IsLetter(ch) || (ch == '*' && i == 0) || (unicode.IsDigit(ch) && i > 0)
}

func isrhs(s string) bool {
	for i, r := range []rune(s) {
		if !isrhsrune(r, i) {
			return false
		}
	}
	if s[0] == '*' && len(s) == 1 {
		return false
	}
	return true
}

type rhs struct {
	Ptr  bool
	Type string
}

type def struct {
	Lhs string
	Rhs []rhs
}

type method struct {
	Ptr    bool
	Recv   string
	Name   string
	Sig    *types.Signature
	SigStr string
}

func (m method) String() string {
	var ptr string
	if m.Ptr {
		ptr = "*"
	}
	return fmt.Sprintf("func (_ %s%s) %s%s { panic(\"default implementation\") }\n", ptr, m.Recv, m.Name, m.SigStr)
}

// Def = LhsType "=" RhsType { "|" RhsType } .
// LhsType = identifier .
// RhsType = [ * ] identifier .
func parseDef(s string) (sum def, err error) {
	msg := "declaration must satisfy the form\n" +
		"\tDef = LhsType \"=\" RhsType { \"|\" RhsType } .\n" +
		"\tLhsType = identifier .\n" +
		"\tRhsType = [ * ] identifier .\n"

	// tokenize
	var sc scanner.Scanner
	sc.Init(strings.NewReader(s))
	sc.Mode = scanner.ScanIdents | scanner.SkipComments
	sc.IsIdentRune = isrhsrune
	sc.Error = func(_ *scanner.Scanner, msg string) {
		err = fmt.Errorf(msg)
	}
	var def []string
	for r := sc.Scan(); r != scanner.EOF; r = sc.Scan() {
		def = append(def, sc.TokenText())
	}
	// validate
	if len(def) < 3 || !isrhs(def[0]) || def[1] != "=" || !isrhs(def[2]) {
		return sum, fmt.Errorf(msg)
	}
	sum.Lhs = def[0]
	if def[2][0] == '*' {
		sum.Rhs = append(sum.Rhs, rhs{true, def[2][1:]})
	} else {
		sum.Rhs = append(sum.Rhs, rhs{false, def[2]})
	}
	for i := 3; i < len(def); i += 2 {
		if def[i] != "|" || i+1 == len(def) || !isrhs(def[i+1]) {
			return sum, fmt.Errorf(msg)
		}
		if v := def[i+1]; v[0] == '*' {
			sum.Rhs = append(sum.Rhs, rhs{true, v[1:]})
		} else {
			sum.Rhs = append(sum.Rhs, rhs{false, v})
		}
	}
	return sum, nil
}

// Given a concrete type, determine methods it is missing that prevent it from satisfying the interface type.
// Return an error if a concrete type does not exist, has a field whose name matches the interface method name,
// or has a method with the same name but different signature.
func appendMissing(pkg *packages.Package, methods []method, iface *types.Interface, rhs rhs) ([]method, error) {
	var concrete types.Type
	if o := pkg.Types.Scope().Lookup(rhs.Type); o != nil {
		concrete = o.Type()
	}
	if concrete == nil {
		return nil, fmt.Errorf("no type with name %q", rhs.Type)
	}
	tname := types.TypeString(concrete, types.RelativeTo(pkg.Types))
	for i, n := 0, iface.NumMethods(); i < n; i++ {
		m := iface.Method(i)
		obj, _, _ := types.LookupFieldOrMethod(concrete, rhs.Ptr, m.Pkg(), m.Name())
		f, _ := obj.(*types.Func)
		if obj != nil && f == nil {
			// make sure it is not a method with the same signature
			return nil, fmt.Errorf("type %s already has a field named %s", tname, obj.Name())
		}
		if f != nil && !types.Identical(m.Type(), f.Type()) {
			return nil, fmt.Errorf("type %s already has a method named %s", tname, m.Name())
		}
		if f == nil {
			methods = append(methods, method{
				Ptr:  rhs.Ptr,
				Recv: tname,
				Name: m.Name(),
				Sig:  m.Type().(*types.Signature),
			})
		}
	}
	return methods, nil
}

// Remove duplicate methods for a given type, and update imports as we go.
func clean(pkg *packages.Package, methods []method) ([]method, map[string]struct{}, error) {
	imports := make(map[string]struct{})
	cmp := func(ma, mb method) int {
		if ma.Recv == mb.Recv && ma.Name == mb.Name {
			if types.Identical(ma.Sig, mb.Sig) {
				return 0
			}
			return -1
		}
		return 1
	}
	// O(n log n)
	sort.Slice(methods, func(i, j int) bool {
		// Precedence
		// 1. Receiver
		// 2. Name
		// 3. Signature implies separate equivalence class.
		// 4. a < *a
		mi, mj := methods[i], methods[j]
		if mi.Recv != mj.Recv {
			return mi.Recv < mj.Recv
		}
		if mi.Name != mj.Name {
			return mi.Name < mj.Name
		}
		if !types.Identical(mi.Sig, mj.Sig) {
			return true
		}
		if mi.Ptr != mj.Ptr {
			return mj.Ptr
		}
		return false
	})
	// remove duplicates. O(n)
	var curr int
	for i := 0; i < len(methods); i++ {
		switch c := cmp(methods[curr], methods[i]); {
		case c == -1:
			return nil, nil, fmt.Errorf("method %q defined multiple times", methods[i].Name)
		case curr == i:
			// update imports
			methods[curr].SigStr = types.TypeString(methods[curr].Sig, func(other *types.Package) string {
				if pkg.Types == other {
					return ""
				}
				imports[other.Path()] = struct{}{}
				return other.Name()
			})[4:]
		case c == 0:
			methods = append(methods[:i], methods[i+1:]...)
			i--
		default:
			curr = i
			i--
		}
	}
	return methods, imports, nil
}

func sumgen(def string) error {
	// Parse specified package
	cwd, err := os.Getwd()
	if err != nil {
		return err
	}
	cfg := &packages.Config{
		Mode: packages.NeedName |
			packages.NeedFiles |
			packages.NeedImports |
			packages.NeedTypes,
	}
	pkgs, err := packages.Load(cfg)
	if err != nil {
		return err
	}
	if len(pkgs) != 1 {
		return fmt.Errorf("could not find Go package in current directory")
	}
	pkg := pkgs[0]

	// Parse sum-type definition
	sum, err := parseDef(def)
	if err != nil {
		return err
	}

	// Find interface type declaration
	var iface *types.Interface
	if t := pkg.Types.Scope().Lookup(sum.Lhs); t != nil {
		iface, _ = t.Type().Underlying().(*types.Interface)
	}
	if iface == nil {
		return fmt.Errorf("no interface type with name %q", sum.Lhs)
	}

	// Look up missing methods for each RHS type.
	var methods []method
	for _, rhs := range sum.Rhs {
		if methods, err = appendMissing(pkg, methods, iface, rhs); err != nil {
			return err
		}
	}
	methods, imports, err := clean(pkg, methods)
	if err != nil {
		return err
	}

	// Output source file
	fname := filepath.Base(cwd) + "_sumgen.go"
	var buf *bytes.Buffer
	if _, stat := os.Stat(fname); stat == nil {
		// If DIRNAME_sumgen.go exists, read it into memory
		if b, err := ioutil.ReadFile(fname); err != nil {
			return err
		} else {
			buf = bytes.NewBuffer(b)
		}
	} else {
		// Otherwise write package declaration to memory
		buf = new(bytes.Buffer)
		buf.WriteString(fmt.Sprintf("// Code generated by \"sumgen\"; DO NOT EDIT.\n\npackage %s\n\n", pkg.Name))
	}
	// append methods
	for _, m := range methods {
		buf.WriteString(m.String())
	}
	// parse constucted file
	fset := token.NewFileSet()
	root, err := parser.ParseFile(fset, "", buf, parser.ParseComments)
	if err != nil {
		return err
	}
	// add imports
	for im := range imports {
		astutil.AddImport(fset, root, im)
	}
	// gofmt it and write it to disk
	file, err := os.Create(fname)
	if err != nil {
		return err
	}
	defer file.Close()
	if err := format.Node(file, fset, root); err != nil {
		return err
	}
	return nil
}

func main() {
	log.SetPrefix("sumgen: ")
	log.SetFlags(0)
	flag.Usage = usage
	flag.Parse()
	def := strings.Join(flag.Args(), "")
	if len(def) == 0 {
		usage()
	}
	if err := sumgen(def); err != nil {
		log.Fatal(err)
	}
}
