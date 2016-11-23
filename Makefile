CC=ocamlopt
SRC=m32x.ml

.PHONY: bench clean

m32x: $(SRC)
	$(CC) -unsafe -ccopt -O5 -S -inline 20 -nodynlink $(SRC) -o m32x

bench:
	./m32x sandmark

clean: m32x
	-rm *.o *.cmi *.cmx *.s
	-rm m32x
