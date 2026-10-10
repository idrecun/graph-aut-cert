CXX ?= g++
CXXFLAGS ?= -std=c++20 -O3 -Wall -Wextra

all: solve prove verify

%: %.cpp
	$(CXX) $(CXXFLAGS) $< -o $@

clean:
	rm -f solve prove verify

.PHONY: all clean
