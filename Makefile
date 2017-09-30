CXX=clang++
CXXFLAGS=-g -c -std=c++11 -stdlib=libc++ -O3 -Wall -Wno-unused-function -Wno-unused-variable -fno-rtti `/Users/sumerkohli/llvm/bin/llvm-config --cxxflags --cppflags`
LDFLAGS=-stdlib=libc++ -g -lpthread `/Users/sumerkohli/llvm/bin/llvm-config --ldflags --libs engine --system-libs`
SOURCES=Compiler.cpp Tests.cpp
OBJECTS=$(SOURCES:.cpp=.o)
EXECUTABLE=cc

-include $(OBJECTS:.o=.d)

all: $(SOURCES) $(EXECUTABLE) cc

$(EXECUTABLE): $(OBJECTS)
	$(CXX) $(LDFLAGS) $(OBJECTS) -o $@

.cpp.o:
	$(CXX) $(CXXFLAGS) $< -o $@
	$(CXX) -MM $(CXXFLAGS) $*.cpp > $*.d

test: cc
	./cc -test

git:
	git commit -a
