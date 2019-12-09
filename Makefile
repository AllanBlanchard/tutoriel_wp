all:
	cd french ; make ; cd ..
	cd english ; make ; cd ..

clean:
	cd french ; make clean ; cd ..
	cd english ; make clean ; cd ..
