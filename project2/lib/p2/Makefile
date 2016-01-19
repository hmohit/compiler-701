DEBUG = ../../Debug/lib
# add optLoads.o to the following line when ready
OBJS = setControl.o printCode.o instrMap.o liveVars.o 

$(DEBUG)/P2.so: $(OBJS) flags.h
	mkdir -p $(DEBUG)
	g++ $(OBJS) -shared -o $@ -fPIC

%.o: %.cpp flags.h
	g++ -c -fno-rtti `llvm-config --cppflags` -g -fPIC $< -o $@

clean:
	rm -f $(DEBUG)/P2.so $(OBJS)
