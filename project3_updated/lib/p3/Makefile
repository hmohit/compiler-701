DEBUG = ../../Debug/lib
# add optLoads.o to the following line when ready
OBJS = setControl.o printCode.o instrMap.o loopInv.o naturalLoop.o 

$(DEBUG)/P3.so: $(OBJS) flags.h naturalLoop.h
	mkdir -p $(DEBUG)
	g++ $(OBJS) -shared -o $@ -fPIC

%.o: %.cpp flags.h
	g++ -c -fno-rtti `llvm-config --cppflags` -g -fPIC $< -o $@

clean:
	rm -f $(DEBUG)/P3.so $(OBJS)
