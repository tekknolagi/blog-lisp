all: transformer binary
	./testfile.native
	# ./lam.native
	# ./mylist.native
	# ./app.native

transformer:
	ocamlbuild -package "compiler-libs.common" astgen.native

binary:
	ocamlbuild -pp "./astgen.native" testfile.native
	# ocamlbuild -pp "./astgen.native" lam.native
	# ocamlbuild -pp "./astgen.native" mylist.native
	# ocamlbuild -pp "./astgen.native" app.native
