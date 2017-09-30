#include "Common.h"
#include "Compiler.h"

const std::string test_dir = "tests"; // test directory path
const std::string out_name = "out"; // output file name

std::ifstream ifp;
bool expect_compiled = true; // whether to expect successful compilation or not
std::string expected_output = "";

void ReadInfo(void){
	expected_output = "";
	expect_compiled = true;
	assert(ifp.is_open() && ("No test output file provided!"));
	std::string buf;
	std::getline(ifp, buf);
	int fst = atoi(buf.c_str());
	assert((!fst || (fst == 1)) && ("Badly formed first line!"));
	expect_compiled = (fst == 1);
	/*int c = 0;
	while(std::getline(ifp, buf)){
		printf("#%d: |%s|\n", c, buf.c_str());
		if(c) expected_output.push_back('\n');
		++c;
		expected_output += buf;
	}*/
	char on;
	while((on = ifp.get()) != EOF){
		expected_output.push_back(on);
	}
	//printf("|%s|\n", expected_output.c_str());
	ifp.close(); // close info file
}

int Failed(int i){
	printf("%sFailed test #%d!%s\n", BOLDRED, i, RESET);
	return 1;
}

int RunTests(void){
	std::stringstream ss;
	int exit_status = 0;
	char buf[256];
	std::string outp = "";
	bool cont = true;
	for(int i = 1; (cont); i++){
		ss.str("");
		ss << "tests/Test" << i;
		ifp.open(ss.str() + ".out", std::ifstream::in);
		ss << ".txt";
		ReadInfo();
		pid_t pid = fork();
		assert(pid >= 0);
		if(pid == 0){ // child
			int ret = Compile(ss.str(), out_name);
			::exit(ret);
		} else { // parent
			wait(&exit_status);
			int s = WEXITSTATUS(exit_status);
			if((!s && !expect_compiled) || (s && expect_compiled)){
				printf("%sIncorrect compilation status.%s\n", BOLDRED, RESET);
				return Failed(i); // failed
			}
			if(expect_compiled){
				outp = ""; // clear prev. output
				FILE* cmd = popen(("./" + out_name).c_str(), "r");
				if(!cmd){
					printf("%sCould not execute output file!%s\n", BOLDRED, RESET);
					return Failed(i); // failed
				}
				while(fgets(buf, (sizeof(buf) - 1), cmd) != NULL){
					outp += std::string(buf);
				}
				pclose(cmd); // close command
				if(outp != expected_output){
					printf("|%s|%s|\n", outp.c_str(), expected_output.c_str());
					printf("%sIncorrect output recorded.%s\n", BOLDRED, RESET);
					return Failed(i); // failed
				}
			}
			printf("%sPassed test #%d.%s\n", BOLDCYAN, i, RESET);
		}
		ss.str("");
		ss << "tests/Test" << (i + 1) << ".txt";
		ifp.open(ss.str(), std::ifstream::in);
		if(!ifp.is_open()){
			cont = false;
		} else ifp.close();
	}
	printf("%sPassed all tests!%s\n", BOLDCYAN, RESET);
	return 0;
}






























