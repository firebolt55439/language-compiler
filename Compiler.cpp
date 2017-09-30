#include "Common.h"
#include "Compiler.h"
#include "Tests.h"

#include "llvm/Analysis/Passes.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"
#include "llvm/ExecutionEngine/JIT.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/PassManager.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/raw_os_ostream.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Transforms/Scalar.h"

using namespace llvm;

// Lexer/Scanner: //

enum Token {
	tok_eof = -1, // funnily enough, this is the actual value of EOF (at least on Unix)
	// declarations
	tok_func = -2, // fn
	tok_def = -3, // def
	tok_typedef = -4, // typedef
	tok_extern = -5, // external
	tok_import = -6, // import
	tok_let = -9, // let
	tok_set = -10, // set -- DEPRECATED
	tok_if = -12, // if
	tok_else = -13, // else
	tok_while = -14, // while
	tok_return = -16, // return
	tok_dec = -18, // dec
	tok_for = -19, // for
	// "primary" - data, parameters, and more
	tok_id = -7, // an ID/identifier - a string, etc.
	tok_num = -8, // a number (e.g. 1, 65535, 3.14159)
	tok_op = -11, // an operator (e.g. +, *, >=)
	tok_elipsis = -15, // elipsis (e.g. ...)
	tok_quoted_id = -17, // quoted ID (e.g. "test", "Hello, World!\n")
	tok_cast_to = -20, // cast_to --> used for explicit casts to a specific type
	tok_unary_op = -21, // a unary operator (e.g. &, *, -, etc.)
	tok_struct = -22, // struct
	tok_size_of = -23, // sizeof
	tok_func_ptr = -24, // func_ptr
	tok_func_ptr_to = -25, // func_ptr_to
	tok_array_ptr = -26, // array_ptr
	tok_class = -27 // class
};

struct FileLocation;
class ExprAST;
static std::string IdStr; // current identifier - will be filled in if it is a tok_id
static double NumVal; // current number value - will be filled in if it is a tok_num - can be casted to int, etc. as requested or specified
static std::string LastOp = ""; // current operator recognized - will be filled in if it is a tok_op

static std::string FileData; // contents of file provided
static int LastIndex = 0; // index on for the FileData
static int LastLastIndex = 0; // index before last token was consumed
static int LastChar = ' '; // let the gettok function remember the last character read
static int FileDataLength; // length of FileData - calculated once
static bool InString = false; // check if currently in a string
static bool had_dec_point = false; // if the number scanned in had a decimal point

static std::vector<std::tuple<int, std::string> > line_starts; // the starts of lines in the included files
static std::map<std::string, int> BinOpPrec; // binary operator precedence --> and as such, functions as the list of registered binary operators
static std::map<char, bool> UnaryOps; // registered unary operators (limited to length 1, no precedence needed)
static std::map<ExprAST*, FileLocation*> exprLocation; // the map for ExprAST => FileLocation
// FIXME/TODO: Add lexer string support --> see identifier string "overload" // UPDATE: Not sure about this (<--) note?

class ExprAST;

void Error(std::string str, ExprAST* ind = NULL);
void ErrorC(const char* str);
void ErrorF(const char* fmt, ...); // forward declarations of error functions

void Warn(std::string msg){
	fprintf(stderr, "%sWarning: %s%s\n", BOLDYELLOW, RESET, msg.c_str());
}

static char readchar(void){
	if(LastIndex >= FileDataLength) return EOF; // EOF = end of file
	return FileData[LastIndex++];
}

static char peekchar(void){
	if(LastIndex >= FileDataLength) return EOF; // EOF = end of file (no more data to be read)
	return FileData[LastIndex]; // return, but without incrementing the LastIndex
}

bool CouldBeOp(char on){
	// Returns true if the character given could be the first character of a multi-character operator,
	// or if it is an operator by itself.
	char bf[2] = { on, '\0' };
	std::string str = std::string(bf);
	if(BinOpPrec.find(str) != BinOpPrec.end()) return true; // is an operator by itself
	for(std::map<std::string, int>::iterator it = BinOpPrec.begin(); it != BinOpPrec.end(); it++){
		if(str[0] == (it->first)[0]) return true; // is first character of multi-character operator
	}
	return false; // not found anywhere
}

std::tuple<int, std::string> GetCurrentLine(unsigned int ind){
	// For use with error messages primarily - returns actual line number for an index (numbering starts at 1) as well as the filename for it
	if(!line_starts.size()) return std::make_tuple(0, "(file not found)");
	unsigned int line_on = 0;
	std::string last_file = std::get<1>(line_starts[0]);
	//printf("Given ind: |%u|\n", ind);
	for(unsigned int i = 0; i < line_starts.size(); i++, line_on++){
		auto on = line_starts[i];
		//printf("Current tuple at line #%u: <%d, %s>\n", line_on, std::get<0>(on), std::get<1>(on).c_str());
		std::string str_on = "";
		if((str_on = std::get<1>(on)) != last_file){
			last_file = str_on;
			line_on = 1;
		}
		if(ind <= (unsigned int) std::get<0>(on)){
			int ret_ln = (signed int)(line_on); // line #
			//printf("Found line at tuple<%d, %s>\n", std::get<0>(on), std::get<1>(on).c_str());
			return std::make_tuple(ret_ln, std::get<1>(on)); // found it
		}
	}
	return std::make_tuple((int) line_on, std::get<1>(line_starts[line_starts.size() - 1])); // otherwise is on last line
}

static int gettok(void){
	// Return the next token from the file data.
	// Skip whitespace.
	while(isspace(LastChar)){
		LastChar = readchar();
	}
	if(LastChar == '"') InString = !InString;
	LastLastIndex = (LastIndex - 1); // skip whitespace before this (minus one due to LastChar going one ahead)
	// Recognize ID's and specific keywords (e.g. fn, def)
	if(isalpha(LastChar) || (LastChar == '_')){
		// identifier 
		// 	::= [a-zA-Z_][a-zA-Z0-9_]*
		//	::= '"' (character*) '"' // returns only the (character*) part, not the quotes
		IdStr = LastChar;
		while((LastChar = readchar())){
			if(!(isalnum(LastChar) || (LastChar == '_'))) break;
			IdStr += LastChar;
		}
		if(IdStr == "fn") return tok_func;
		if(IdStr == "def") return tok_def;
		if(IdStr == "typedef") return tok_typedef;
		if(IdStr == "external") return tok_extern;
		if(IdStr == "extern") return tok_extern;
		if(IdStr == "import") return tok_import;
		if(IdStr == "let") return tok_let;
		if(IdStr == "set"){
			Warn("A 'set' is no longer recognized.");
			//return tok_set;
		}
		if(IdStr == "if") return tok_if;
		if(IdStr == "else") return tok_else;
		if(IdStr == "while") return tok_while;
		if(IdStr == "return") return tok_return;
		if(IdStr == "dec") return tok_dec;
		if(IdStr == "for") return tok_for;
		if(IdStr == "cast") return tok_cast_to;
		if(IdStr == "struct") return tok_struct;
		if(IdStr == "sizeof") return tok_size_of;
		if(IdStr == "func_ptr") return tok_func_ptr;
		if(IdStr == "func_ptr_to") return tok_func_ptr_to;
		if(IdStr == "array_ptr") return tok_array_ptr;
		if(IdStr == "class") return tok_class;
		return tok_id;
	}
	// Recognize numbers or numeric constants (e.g. 1.0, 65, 3.14159)
	if(isdigit(LastChar)){ // number = [0-9][0-9.]+
		std::string NumStr;
		do {
			NumStr += LastChar;
			LastChar = readchar();
		} while (isdigit(LastChar) || (LastChar == '.'));
		NumVal = atof(NumStr.c_str());
		had_dec_point = (NumStr.find('.') != std::string::npos) ? true : false;
		return tok_num;
	}
	// Recognize and ignore comments.
	if((LastChar == '#') || ((LastChar == '/') && ((peekchar() == '/') || (peekchar() == '*')))){
		// Supports Python-style comments (#), and C/C++-style line comments (//).
		char sl_char = '\0';
		if(LastChar == '/') sl_char = readchar(); // record second char to test whether is "//" or "/*"
		if((sl_char == '\0') || (sl_char == '/')){
			do {
				LastChar = readchar();
			} while((LastChar != EOF) && (LastChar != '\n') && (LastChar != '\r')); // '\r' is for CRLF in Windows
		} else {
			char PrevChar = LastChar;
			do {
				PrevChar = LastChar;
				LastChar = readchar();
				//printf("On |%c| |%c| for comment.\n", PrevChar, LastChar);
			} while((!((PrevChar == '*') && (LastChar == '/'))) && (LastChar != EOF));
			LastChar = readchar(); // read one more
		}
		if(LastChar != EOF) return gettok(); // return next valid token
		return tok_eof; // otherwise return EOF
	}
	// Recognize an elipsis (e.g. '...')
	if(LastChar == '.'){
		int orig_index = LastIndex;
		if(peekchar() == '.'){
			readchar(); // consume first '.'
			if(peekchar() == '.'){
				readchar();
				LastChar = readchar();
				return tok_elipsis;
			}
		}
		LastIndex = orig_index; // if not a match for an elipsis, restore previous state
	}
	// Recognize a string (e.g. "test")
	if(LastChar == '"'){ // [\"][* (NOT \")]*[\"]
		std::string got;
		while(true){
			LastChar = readchar();
			if((LastChar == '"') || (LastChar == EOF)) break;
			got.push_back(LastChar);
		}
		if(LastChar == EOF) Error("Reached EOF while reading a string."); // TODO: Better error here, fix-it (suggest inserting before first consumed semicolon?)
		LastChar = readchar(); // consume the '"'
		// Now handle any escape sequences by converting to ASCII value (e.g. "\n" --> '\n' or 10)
		std::string res = "";
		for(unsigned int i = 0; i < got.length(); i++){
			char on = got[i];
			if((on != '\\') || ((i + 1) >= got.length())){
				res.push_back(on);
			} else {
				char next = got[i + 1];
				if(next == 'n') res.push_back('\n');
				else if(next == 'r') res.push_back('\r');
				else if(next == 'b') res.push_back('\b');
				else if(next == 't') res.push_back('\t');
				i++;
			}
		}
		IdStr = res;
		return tok_quoted_id;
	}
	// Recognize operators of any length (e.g. *, ++, >=)
	if(CouldBeOp(LastChar)){
		int orig_index = LastIndex;
		printf("Recognized a possible operator.\n");
		char orig_char = LastChar;
		std::vector<std::string> possibilities; // all possibilities
		for(std::map<std::string, int>::iterator it = BinOpPrec.begin(); it != BinOpPrec.end(); it++){
			if((it->first)[0] == LastChar) possibilities.push_back(it->first);
		}
		std::string str(1, LastChar); // the string we may be adding to
		std::vector<std::tuple<std::string, int, char> > matches; // matches --> stores match name, file index position, and LastChar
		while(true){
			std::vector<std::string> next; // next possibilities
			for(std::vector<std::string>::iterator it = possibilities.begin(); it != possibilities.end(); it++){
				if(str == *it){
					// Have a full match, let's store it.
					matches.push_back(std::make_tuple(*it, LastIndex, LastChar));
				} else if(str == (*it).substr(0, str.length())){
					next.push_back(*it);
				}
			}
			if(!next.size()) break; // if no more possibilities, break for processing of confirmed matches
			possibilities = next; // otherwise, change out possibilities for the recomputed set
			LastChar = readchar();
			str.push_back(LastChar); // add another char
		}
		//if(!matches.size()) ErrorF("Unrecognized operator sequence starting with |%c|.", orig_char);
		if(matches.size() > 1){
			std::vector<std::tuple<std::string, int, char> > final_matches;
			int max_len = 0;
			for(std::vector<std::tuple<std::string, int, char> >::iterator it = matches.begin(); it != matches.end(); it++){
				std::tuple<std::string, int, char>& on = *it;
				if((signed int) std::get<0>(on).length() > max_len) max_len = std::get<0>(on).length();
			}
			for(std::vector<std::tuple<std::string, int, char> >::iterator it = matches.begin(); it != matches.end(); it++){
				std::tuple<std::string, int, char>& on = *it;
				if((signed int) std::get<0>(on).length() == max_len) final_matches.push_back(on);
			}
			matches = final_matches;
		}
		if(matches.size() > 1){ // great error, just not used much if at all - kept for legacy reasons
			fprintf(stderr, "Ambiguous operator sequence starting with |%c|.\n", orig_char);
			for(std::vector<std::tuple<std::string, int, char> >::iterator it = matches.begin(); it != matches.end(); it++){
				fprintf(stderr, "\tCandidate sequence |%s|.\n", std::get<0>(*it).c_str());
			}
			Error("Clarify operator sequence by use of parantheses.");
		}
		if(matches.size()){
			std::tuple<std::string, int, char>& match = matches[0];
			LastOp = std::get<0>(match); // set operator for parsing
			printf("Recognized operator match |%s|.\n", LastOp.c_str());
			LastIndex = std::get<1>(match); // restore file index
			LastChar = std::get<2>(match); // restore LastChar
			LastChar = readchar(); // read one more character to set up for next call
			return tok_op; // return operator token
		} else {
			printf("Was not an operator match, restoring previous state...\n");
			LastChar = orig_char;
			LastIndex = orig_index;
		}
	} else printf("Rejected |%c| as a possible operator start.\n", LastChar);
	// Recognize enabled unary operators of length 1.
	if((UnaryOps.find(LastChar) != UnaryOps.end()) && UnaryOps.at(LastChar)){ // relies on "short-circuiting" behavior
		LastOp = "";
		LastOp.push_back(LastChar);
		LastChar = readchar();
		return tok_unary_op;
	}
	// Check for EOF - but do NOT eat it - or bad things happen.
	if(LastChar == EOF) return tok_eof;
	// Not recognized - we'll return the character as its ASCII value.
	// Note: This is the reason the enum Token has all negative values - for differentiation between a char and a token.
	int ThisChar = (signed int) LastChar; // save current character
	LastChar = readchar(); // get the next char
	return ThisChar; // return this one
}

// Abstract Syntax Tree/AST: //

struct CGReturnType {
	// Codegen return type struct --> stores information about returned value as well
	Value* val;
	llvm::Type* type; // the llvm type of val
	bool is_alloca; // if it is an AllocaInst
	bool is_func; // if it is a Function
	
	CGReturnType(Value* vl, llvm::Type* tp, bool alloca, bool isfunc) :
		val(vl), type(tp), is_alloca(alloca), is_func(isfunc) {
			//
		}
};

struct FileLocation {
	// This keeps track of the start => end for the file index
	// so as to aid in error and diagnostic messages.
	int st = 0; // start
	int et = 0; // end
	
	FileLocation(int s, int e){
		st = s;
		et = e;
	}
};

// This is the base class, from which all classes must be derived.
class ExprAST {
	public:
		enum ExprKind {
			E_Number,
			E_Variable,
			E_Binary,
			E_Unary,
			E_Call,
			E_Type,
			E_FuncPtr,
			E_ArrayPtr,
			E_FuncRef,
			E_SizeOf,
			E_StructType,
			E_Struct,
			E_NewClass,
			E_Cast,
			E_Line,
			E_Prototype,
			E_Function,
			E_Class,
			E_If,
			E_While,
			E_For,
			E_Array,
			E_String
		};
		
		ExprKind getKind(void) const {
			return Kind;
		}
		
		virtual ~ExprAST(void){
			// Virtual destructor.
		}
		
		virtual CGReturnType* Codegen(void) = 0; // should be implemented in all derived classes
	protected:
		ExprAST(ExprKind K) : Kind(K) {
			// Protected constructor - cannot be called directly from instances - rather, only from derived classes.
		}
	private:
		const ExprKind Kind;
};

// This class stores a numeric constant (e.g. 3.14)
class NumberExprAST : public ExprAST {
	double val; // stored value as a double to allow storing pretty much any type
	bool dec_point; // if there was a decimal point or not
	public:
		NumberExprAST(double new_val) : ExprAST(E_Number), val(new_val) {
			dec_point = false;
		}
		
		void RegisterDecimal(void){
			dec_point = true;
		}
		
		CGReturnType* Codegen(void);
		
		static bool classof(const ExprAST* E){ return E->getKind() == E_Number; }
};

// This class stores a variable reference (e.g. "argc").
class VariableExprAST : public ExprAST {
	std::string name; // the name of the variable referenced (should be an ID)
	std::vector<ExprAST*> indices; // indices for array - if/a
	ExprAST* post_incr; // for post incr/decrement, a BinaryExprAST pointer (NULL if not used)
	public:
		VariableExprAST(const std::string& new_name) : ExprAST(E_Variable), name(new_name) {
			// nope
		}
		
		void RegisterIndex(ExprAST* Index){
			indices.push_back(Index);
		}
		
		void RegisterIndex(std::vector<ExprAST*>& Indices){
			indices = Indices;
		}
		
		void RegisterPost(ExprAST* post){
			post_incr = post;
		}
		
		std::string GetName(void){
			// This "getter" is provided since unrecognized identifiers are parsed as VariableExprAST's.
			return name;
		}
		
		CGReturnType* Codegen(void);
		
		static bool classof(const ExprAST* E){ return E->getKind() == E_Variable; }
};

// This class stores a binary expression as well as its associated binary operator.
class BinaryExprAST : public ExprAST {
	std::string Op; // the operator
	ExprAST* LHS; // the left-hand side
	ExprAST* RHS; // the right-hand side
	public:
		BinaryExprAST(std::string op, ExprAST* lhs, ExprAST* rhs) : ExprAST(E_Binary), Op(op), LHS(lhs), RHS(rhs) {
			// Move along, move along...
		}
		
		CGReturnType* Codegen(void);
		
		static bool classof(const ExprAST* E){ return E->getKind() == E_Binary; }
};

// This class stores a unary expression along with its associated unary operator.
class UnaryExprAST : public ExprAST {
	std::string Op; // the operator
	ExprAST* on; // the expression the operation is being applied to
	public:
		UnaryExprAST(std::string op, ExprAST* sub) : ExprAST(E_Unary), Op(op), on(sub) {
			// no... just no
		}
		
		CGReturnType* Codegen(void);
		
		static bool classof(const ExprAST* E){ return E->getKind() == E_Unary; }
};

// This class stores a function call along with any parameters and the callee's name.
class CallExprAST : public ExprAST {
	std::string Callee;
	std::vector<ExprAST*> Args;
	public:
		CallExprAST(const std::string &callee, std::vector<ExprAST*> &args) : ExprAST(E_Call), Callee(callee), Args(args) {
			// [null]
		}
		
		CGReturnType* Codegen(void);
		
		static bool classof(const ExprAST* E){ return E->getKind() == E_Call; }
};

// This class stores a "type" reference.
// Note: During code generation, it returns an LLVM type rather than a Value.
class TypeExprAST : public ExprAST {
	std::string Type;
	int depth; // pointer "depth" -- number of *'s trailing the pointer type (e.g. char** = depth 2)
	public:
		TypeExprAST(const std::string& type) : ExprAST(E_Type), Type(type) {
			depth = 0;
		}
		
		void SetDepth(int new_depth){
			depth = new_depth;
		}
		
		CGReturnType* Codegen(void);
		
		static bool classof(const ExprAST* E){ return E->getKind() == E_Type; }
};

// This class stores a function pointer type reference (e.g. func_ptr(void, int) is a function that returns void and takes an 'int' parameter).
class FuncPtrExprAST : public ExprAST {
	std::vector<TypeExprAST*> types; // [0] => return type, [1 ... size] => params
	public:
		FuncPtrExprAST(std::vector<TypeExprAST*>& tp) : ExprAST(E_FuncPtr), types(tp) {
			//
		}
		
		CGReturnType* Codegen(void);
		
		static bool classof(const ExprAST* E){ return E->getKind() == E_FuncPtr; }
};

// This class stores an array type reference (e.g. array_ptr(int, 5) is an int array of size 5)
class ArrayPtrExprAST : public ExprAST {
	TypeExprAST* type;
	ExprAST* size;
	public:
		ArrayPtrExprAST(TypeExprAST* tp, ExprAST* sz) : ExprAST(E_ArrayPtr), type(tp), size(sz) {
			//
		}
		
		CGReturnType* Codegen(void);
		
		static bool classof(const ExprAST* E){ return E->getKind() == E_ArrayPtr; }
};

// This class stores a function reference (e.g. func_ptr_to(test_func))
class FuncRefExprAST : public ExprAST {
	std::string name; // function name
	public:
		FuncRefExprAST(std::string nm) : ExprAST(E_FuncRef), name(nm) {
			//
		}
		
		CGReturnType* Codegen(void);
		
		static bool classof(const ExprAST* E){ return E->getKind() == E_FuncRef; }
};

// This class stores a "sizeof" expression along with its associated type.
class SizeOfExprAST : public ExprAST {
	TypeExprAST* type;
	public:
		SizeOfExprAST(TypeExprAST* tp) : ExprAST(E_SizeOf), type(tp) {
			//
		}
		
		CGReturnType* Codegen(void);
		
		static bool classof(const ExprAST* E){ return E->getKind() == E_SizeOf; }
};

// This class stores a "struct" declaration (not instantiation).
// Note: During code generation, it returns an LLVM type rather than a Value.
class StructTypeExprAST : public ExprAST {
	std::string struct_name; // e.g. 'node_t'
	std::vector<TypeExprAST*> types; // e.g. { int, char }
	std::vector<std::string> names; // e.g. { an_integer, a_character }
	public:
		StructTypeExprAST(const std::string& sn, std::vector<TypeExprAST*>& tp, std::vector<std::string>& nm) : ExprAST(E_StructType), struct_name(sn), types(tp), names(nm) {
			// EOF - end of *function*
		}
		
		CGReturnType* Codegen(void);
		
		static bool classof(const ExprAST* E){ return E->getKind() == E_StructType; }
};

// This class stores a "struct" insantiation.
class StructExprAST : public ExprAST {
	std::string name; // name of struct
	TypeExprAST* struct_type; // struct type
	public:
		StructExprAST(const std::string& nm, TypeExprAST* st) : ExprAST(E_Struct), name(nm), struct_type(st) {
			//
		}
		
		CGReturnType* Codegen(void);
		
		static bool classof(const ExprAST* E){ return E->getKind() == E_Struct; }
};

// This class stores a "class" instantiation.
class NewClassExprAST : public ExprAST {
	// TODO: Destructors with VarScopes going out of context
	std::string name;
	TypeExprAST* type; // class "struct" type
	std::vector<ExprAST*> ctor_args; // constructor arguments
	public:
		NewClassExprAST(const std::string& nm, TypeExprAST* tp, std::vector<ExprAST*>& ct) : ExprAST(E_NewClass), name(nm), type(tp), ctor_args(ct) {
			//
		}
		
		CGReturnType* Codegen(void);
		
		static bool classof(const ExprAST* E){ return E->getKind() == E_NewClass; }
};

// This class stores an explicit cast of a value to a specific type.
class CastExprAST : public ExprAST {
	TypeExprAST* type_to; // type being casted to
	ExprAST* value; // value being casted to specified type
	public:
		CastExprAST(TypeExprAST* t_to, ExprAST* val) : ExprAST(E_Cast), type_to(t_to), value(val) {
			// Nada
		}
		
		CGReturnType* Codegen(void);
		
		static bool classof(const ExprAST* E){ return E->getKind() == E_Cast; }
};

// This class stores a "line".
class LineExprAST : public ExprAST {
	std::string LHS; // left hand side (lvalue)
	TypeExprAST* ltype; // LHS type
	std::vector<ExprAST*> LHS_indices; // LHS indices for GEP instruction if/a (e.g. set arr[0] = <...>)
	ExprAST* RHS; // right hand side (rvalue)
	bool is_declaration; // if it is a declaration - if false, it is a mutation
	public:
		LineExprAST(std::string lhs, ExprAST* rhs) : ExprAST(E_Line), LHS(lhs), RHS(rhs) {
			is_declaration = false;
		}
		
		void RegisterDeclaration(TypeExprAST* l_type){
			is_declaration = true;
			ltype = l_type;
		}
		
		void RegisterIndices(std::vector<ExprAST*>& indices){
			LHS_indices = indices;
		}
		
		CGReturnType* Codegen(void);
		
		static bool classof(const ExprAST* E){ return E->getKind() == E_Line; }
};
	

// This class stores the prototype for a function, which captures
// the name of the function, the parameters and their associated types,
// and the argument names as well as any additional attributes.
class PrototypeAST : public ExprAST {
	public: // this is to allow modifications as needed by, for example, classes
	std::string Name; // function name
	bool is_extern; // if this is an "external" definition
	std::string ExternType; // if is external, then what type - e.g. "C"
	std::vector<std::string> Args; // name of the arguments passed
	std::vector<TypeExprAST*> Args_Type; // type of arguments passed for each argument
	std::vector<std::string> Attrs; // any additional attributes specified
	TypeExprAST* RetType; // return type
	bool isVarArg; // if this is a vararg function (has a tok_elipsis at end) or not
	// methods
		PrototypeAST(const std::string& name, const std::vector<std::string>& args, const std::vector<TypeExprAST*>& args_type, const std::vector<std::string>& attrs)
			: ExprAST(E_Prototype), Name(name), Args(args), Args_Type(args_type), Attrs(attrs) {
				isVarArg = is_extern = false;
			}
		
		void RegisterExtern(std::string extern_type){
			is_extern = true;
			ExternType = extern_type;
		}
		
		void RegisterReturnType(TypeExprAST* ret_type){
			RetType = ret_type;
		}
		
		void RegisterVarArg(void){
			isVarArg = true;
		}
		
		CGReturnType* Codegen(void);
		
		static bool classof(const ExprAST* E){ return E->getKind() == E_Prototype; }
};

// This class represents the definition of a new function, along with its body.
class FunctionAST : public ExprAST {
	PrototypeAST* Proto; // the prototype of it
	std::vector<ExprAST*> Body; // the function body
	public:
		FunctionAST(PrototypeAST* proto, std::vector<ExprAST*>& body) : ExprAST(E_Function), Proto(proto), Body(body) {
			// nothing to do here, really
		}
		
		PrototypeAST* GetProto(void){
			return Proto;
		}
		
		CGReturnType* Codegen(void);
		
		static bool classof(const ExprAST* E){ return E->getKind() == E_Function; }
};

// This class stores a class declaration, as well as its associated members.
class ClassExprAST : public ExprAST {
	std::string Name; // class name
	std::vector<std::tuple<TypeExprAST*, std::string> > ivars; // class instance variables
	std::vector<FunctionAST*> members; // class methods
	public:
		ClassExprAST(const std::string& nm, const std::vector<std::tuple<TypeExprAST*, std::string> >& ivr, const std::vector<FunctionAST*>& mbs) : 
			ExprAST(E_Class), Name(nm), ivars(ivr), members(mbs) {
			//
		}
		
		CGReturnType* Codegen(void);
		
		static bool classof(const ExprAST* E){ return E->getKind() == E_Class; }
};

// This class represents an "if" with an optional "else" conditional.
class IfExprAST : public ExprAST {
	ExprAST* cond; // the condition to be evaluated
	std::vector<ExprAST*> if_true; // the "if true" or "then" branch
	std::vector<ExprAST*> if_false; // the "if false" or "else" branch
	public:
		IfExprAST(ExprAST* Cond, ExprAST* IfTrue, ExprAST* IfFalse) : ExprAST(E_If), cond(Cond) {
			if_true.push_back(IfTrue);
			if_false.push_back(IfFalse);
		}
		
		IfExprAST(ExprAST* Cond, std::vector<ExprAST*> IfTrue, std::vector<ExprAST*> IfFalse) : ExprAST(E_If), cond(Cond), if_true(IfTrue), if_false(IfFalse) {
			// not much... at all
		}
		
		CGReturnType* Codegen(void);
		
		static bool classof(const ExprAST* E){ return E->getKind() == E_If; }
};

// This class represents a "while" loop.
class WhileExprAST : public ExprAST {
	ExprAST* cond; // the condition to be evaluated at the start of every loop
	std::vector<ExprAST*> body; // the body of the while loop
	public:
		WhileExprAST(ExprAST* Cond, ExprAST* Body) : ExprAST(E_While), cond(Cond) {
			body.push_back(Body);
		}
		
		WhileExprAST(ExprAST* Cond, std::vector<ExprAST*> Body) : ExprAST(E_While), cond(Cond), body(Body) {
			// nothing - really!
		}
		
		CGReturnType* Codegen(void);
		
		static bool classof(const ExprAST* E){ return E->getKind() == E_While; }
};

// This class represents a "for" loop.
class ForExprAST : public ExprAST {
	ExprAST* init; // the "initialization" part of the loop
	ExprAST* cond; // the condition to be evaluated every time the loop runs
	ExprAST* incr; // the "increment" statement or such
	std::vector<ExprAST*> body; // the body of the for loop
	public:
		ForExprAST(ExprAST* Init, ExprAST* Cond, ExprAST* Incr) : ExprAST(E_For), init(Init), cond(Cond), incr(Incr) {
			// nothing = win
		}
		
		void RegisterBody(ExprAST* Body){
			body.push_back(Body);
		}
		
		void RegisterBody(std::vector<ExprAST*> Body){
			body = Body;
		}
		
		CGReturnType* Codegen(void);
		
		static bool classof(const ExprAST* E){ return E->getKind() == E_For; }
};

// This class stores an array declaration.
class ArrayExprAST : public ExprAST {
	std::string name; // array name
	TypeExprAST* type; // contained type
	std::vector<ExprAST*> size; // size(s) of array dimensions -- must be compile-time constants (e.g. 1+2)
	std::vector<ExprAST*> initial; // for {...}-style declarations, the initial values of the array
	public:
		ArrayExprAST(std::string Name, TypeExprAST* Type) : ExprAST(E_Array), name(Name), type(Type) {
			// nothing... for real
		}
		
		void SetSize(ExprAST* Size){
			size.push_back(Size);
		}
		
		void SetSize(std::vector<ExprAST*>& Size){
			size = Size;
		}
		
		void RegisterInitial(std::vector<ExprAST*>& Initial){
			initial = Initial;
		}
		
		CGReturnType* Codegen(void);
		
		static bool classof(const ExprAST* E){ return E->getKind() == E_Array; }
};

// This class stores a string.
class StringExprAST : public ExprAST {
	std::string value; // the contained string
	public:
		StringExprAST(std::string Value) : ExprAST(E_String), value(Value) {
			// nop
		}
		
		CGReturnType* Codegen(void);
		
		static bool classof(const ExprAST* E){ return E->getKind() == E_String; }
};

// Code Generation Structures //
class Symbol {
	protected:
		Symbol(void){
			// Only derived classes should ever be constructed.
		}
	public:
		virtual ~Symbol(void){
			// Virtual destructor.
		}
};

struct VarSymbol : public Symbol {
	Value* val;
	llvm::Type* type;
	bool is_class_ivar = false; // if this is a class ivar or not (meaning that a class method is referencing its own ivar)
	
	VarSymbol(Value* vl, llvm::Type* tp) : val(vl), type(tp) {
		// [nada]
	}
	
	void RegisterIVar(void){
		is_class_ivar = true;
	}
};

struct FuncSymbol : public Symbol {
	std::vector<llvm::Type*> types;
	bool is_extern;
	Function* func;
	llvm::Type* RetType;
	FunctionType* FuncType;
	
	FuncSymbol(std::vector<llvm::Type*> type, bool isExtern, Function* Func, llvm::Type* ret_type, FunctionType* func_type) :
		types(type), is_extern(isExtern), func(Func), RetType(ret_type), FuncType(func_type) {
			//
		}
};

// Token Buffer + Helper Functions: //
static int CurTok; // current parser token

static int getNextToken(void){
	return (CurTok = gettok());
}

static int GetStart(ExprAST* expr){
	return exprLocation[expr]->st;
}

static int GetEnd(ExprAST* expr){
	return exprLocation[expr]->et;
}

static std::map<FuncSymbol*, PrototypeAST*> function_map; // a mapping for a function symbol to a function AST node (used primarily for errors)
static std::map<Function*, FuncSymbol*> function_sym_map;

void NoteFunction(FuncSymbol* func, std::string func_msg = "function '%s' declared here:"){
	if(function_map.find(func) == function_map.end()){
		fprintf(stderr, "Could not find function for given func symbol with (possibly mangled) name '%s'.\n", ((Value*) func->func)->getName().data());
		return;
	}
	ExprAST* ind = (ExprAST*) function_map.at(func); // is a PrototypeAST*
	// Get borders of function //
	int st = GetStart(ind);
	int et = GetEnd(ind);
	auto slh = GetCurrentLine(st);
	int sl = std::get<0>(slh);
	auto elh = GetCurrentLine(et);
	int el = std::get<0>(elh);
	assert(std::get<1>(slh) == std::get<1>(elh));
	std::cerr << BOLDWHITE << std::get<1>(slh) << ":" << sl;
	if(sl != el) std::cerr << "-" << el;
	std::cerr << ": " << RESET;
	std::cerr << BLUECOLOR << "note: " << RESET;
	fprintf(stderr, (func_msg + "\n").c_str(), ((PrototypeAST*) ind)->Name.c_str());
	std::cerr <<  "\t'" << CYANCOLOR;
	std::string slice = FileData.substr(st, (et - st));
	if(slice.find('\n')) slice = slice.substr(0, (slice.find('\n') - 1));
	std::cerr << slice << RESET << "'" << "\n\n";
}

void NoteFunction(Function* func, std::string func_msg = "function '%s' declared here:"){
	assert(function_sym_map.find(func) != function_sym_map.end());
	NoteFunction(function_sym_map[func], func_msg);
}

void Error(std::string str, ExprAST* ind){
	// TODO: Add underlining for start and end
	if(!ind || (exprLocation.find(ind) == exprLocation.end())){
		// Parser Error
		std::tuple<int, std::string> on = GetCurrentLine(LastIndex);
		fprintf(stderr, "%s%s:%d:%s %sError: %s%s\n", BOLDWHITE, std::get<1>(on).c_str(), std::get<0>(on), RESET, BOLDRED, RESET, str.c_str());
	} else {
		// Code Generation Error
		assert(exprLocation.find(ind) != exprLocation.end());
		int st = GetStart(ind);
		int et = GetEnd(ind);
		auto slh = GetCurrentLine(st);
		int sl = std::get<0>(slh);
		auto elh = GetCurrentLine(et);
		int el = std::get<0>(elh);
		assert(std::get<1>(slh) == std::get<1>(elh));
		std::stringstream ss;
		ss << BOLDWHITE;
		ss << std::get<1>(slh) << ":";
		ss << sl;
		if(sl != el) ss << "-" << el;
		ss << " ";
		ss << RESET << " " << BOLDRED; 
		ss << "Error: " << RESET << str;
		ss << "\n";
		//fprintf(stderr, "%s%d:%s %sError: %s%s\n", BOLDWHITE, GetCurrentLine(LastIndex), RESET, BOLDRED, RESET, str.c_str());
		std::cerr << ss.str();
		ss.str(""); // clear stringstream
		ss << BLUECOLOR << "\tnote: " << RESET;
		ss << "affected code section:" << "\n";
		ss << "\t'" << CYANCOLOR;
		std::string slice = FileData.substr(st, (et - st));
		if(slice.find('\n')) slice = slice.substr(0, (slice.find('\n') - 1)); // only takes one line
		ss << slice << RESET;
		ss << "'" << "\n";
		std::cerr << ss.str();
	}
	::exit(1);
}

void ErrorC(const char* str){ // "constant" error
	Error(std::string(str));
}

void ErrorF(ExprAST* ind, const char* fmt, ...){ // "formatted" error
	static char* buf = (char*) malloc(512); // only need the memory once
	buf[0] = '\0'; // zero out memory - effectively setting length to 0
	va_list args;
	va_start(args, fmt);
	vsprintf(buf, fmt, args);
	va_end(args);
	Error(std::string(buf), ind);
}

// Parser: //

static ExprAST* ParsePrimary(void); // forward declaration
static LineExprAST* ParseLine(void); // forward declaration
static ExprAST* ParseIfExpr(void); // forward declaration
static ExprAST* ParseWhileExpr(void); // forward declaration
static ExprAST* ParseTypeRef(void); // forward declaration
static ExprAST* ParseForExpr(void); // forward declaration
static ExprAST* ParseExpression(void); // forward declaration
static FunctionAST* ParseDefinition(void); // forward declaration

static std::map<std::string, std::tuple<std::string, int> > typedefs; // user typedefs (new type => old type info + depth)

// numberexpr ::= number
static ExprAST* ParseNumberExpr(void){
	printf("Parsing a number expression...\n");
	// parse a numeric literal
	int st = LastIndex;
	NumberExprAST* Result = new NumberExprAST(NumVal);
	if(had_dec_point) Result->RegisterDecimal();
	getNextToken(); // consume number
	int et = LastIndex;
	exprLocation[Result] = new FileLocation(st, et);
	return (ExprAST*) Result;
}

// Returns the precedence of the current binary operator (CurTok).
static int GetTokPrecedence(void){
	if(!BinOpPrec.size()){
		Error("No binary operators have been defined."); // if no operator has been defined yet, for whatever reason
	}
	if(CurTok != tok_op) return -1;
	if(BinOpPrec.find(LastOp) == BinOpPrec.end()) Error("Invalid operator token recognized.");
	return BinOpPrec[LastOp]; // otherwise return its registered precedence
}

// binoprhs
//	 ::= (op primary)*
static ExprAST* ParseBinOpRHS(int ExprPrec, ExprAST* LHS){
	// Get its precedence.
	printf("Parsing right hand side binary expression...\n");
	//getNextToken();
	while(true){
		int TokPrec = GetTokPrecedence();
		// If this does not bind as tightly, we're done.
		if((TokPrec < ExprPrec) && (TokPrec != 2)) return LHS;
		// Fine, it binds more tightly.
		std::string BinOp = LastOp; // save the operator
		printf("RHS Op |%s| of len |%d|.\n", BinOp.c_str(), (signed int) LastOp.length());
		getNextToken(); // consume operator
		// Parse the primary now.
		ExprAST* RHS = ParsePrimary();
		// If BinOp binds less tightly with the RHS than the operator after RHS, the
		// current operator takes RHS as its LHS.
		int NextPrec = GetTokPrecedence();
		if((TokPrec == NextPrec) && (NextPrec == 2)){
			printf("Compound assignment detected!\n");
			// Handle compound assignment (e.g. x = y = z = 0)
			NextPrec = TokPrec + 1;
			printf("T: %d, N: %d\n", TokPrec, NextPrec);
		}
		if(TokPrec < NextPrec){
			RHS = ParseBinOpRHS((TokPrec + 1), RHS);
		}
		// Merge the LHS and RHS.
		LHS = new BinaryExprAST(BinOp, LHS, RHS);
	}
	printf("Parsed right hand side binary expression.\n");
}

// typedef
//	::= 'typedef' id ':' id ';'
// precond: CurTok is a tok_typedef
static void ParseTypeDef(void){
	// Typedef's are special since they are not part of the AST -
	// more "preprocessor"-based almost.
	if(CurTok != tok_typedef) Error("Expected a 'typedef'.");
	getNextToken(); // consume 'typedef'
	if(CurTok != tok_id) Error("Expected a new type name.");
	std::string type_name = IdStr;
	getNextToken(); // consume type name
	if(CurTok != ':') Error("Expected a colon between the new type name and the source type.");
	getNextToken(); // consume colon
	if(CurTok != tok_id) Error("Expected a source type name.");
	std::string base_type = IdStr;
	getNextToken(); // consume base type
	int rdepth = 0; // "depth" of right hand side (# of *'s)
	while(CurTok == tok_op){
		if(LastOp != "*") Error("Expected '*'.");
		rdepth++;
		getNextToken();
	}
	if(CurTok != ';') Error("Expected a semicolon.");
	getNextToken(); // consume semicolon
	if(typedefs.find(type_name) != typedefs.end()) Error("Cannot redefine type '" + type_name + "'.");
	if(type_name == base_type) Error("Cannot define a type as itself.");
	while(typedefs.find(base_type) != typedefs.end()){
		// Handle statements like:
		// typedef sint : i32;
		// typedef int: sint;
		// for an infinite "loop"
		base_type = std::get<0>(typedefs[base_type]);
	}
	typedefs[type_name] = std::make_tuple(base_type, rdepth); // register typedef
}

// funcptrexpr
//	::= 'func_ptr' '(' (typeref [','])* ')'
static ExprAST* ParseFuncPtrExpr(void){
	// FuncPtrExprAST
	int st = LastIndex;
	if(CurTok != tok_func_ptr) Error("Expected 'func_ptr'.");
	getNextToken();
	if(CurTok != '(') Error("Expected a '(' to specify function pointer arguments.");
	getNextToken();
	std::vector<TypeExprAST*> tp;
	while(CurTok != ')'){
		TypeExprAST* on = (TypeExprAST*) ParseTypeRef();
		if(CurTok == ',') getNextToken();
		tp.push_back(on);
	}
	int et = LastIndex;
	getNextToken(); // consume ')'
	ExprAST* res = new FuncPtrExprAST(tp);
	exprLocation[res] = new FileLocation(st, et);
	return res;
}

// arrayptrexpr
//	::= 'array_ptr' '(' typeref ',' expression ')'
static ExprAST* ParseArrayPtrExpr(void){
	// ArrayPtrExprAST
	int st = LastIndex;
	if(CurTok != tok_array_ptr) Error("Expected 'array_ptr'.");
	getNextToken();
	if(CurTok != '(') Error("Expected a '(' to specify array type arguments.");
	getNextToken();
	TypeExprAST* tp = (TypeExprAST*) ParseTypeRef();
	if(CurTok != ',') Error("Expected a comma.");
	getNextToken();
	ExprAST* expr = ParseExpression();
	if(CurTok != ')') Error("Expected a ')' to close array type arguments.");
	int et = LastIndex;
	getNextToken(); // consume ')'
	ExprAST* res = new ArrayPtrExprAST(tp, expr);
	exprLocation[res] = new FileLocation(st, et);
	return res;
}

// funcrefexpr
//	::= 'func_ptr_to' '(' id ')'
static ExprAST* ParseFuncRefExpr(void){
	// FuncRefExprAST
	int st = LastIndex;
	if(CurTok != tok_func_ptr_to) Error("Expected 'func_ptr_to'.");
	getNextToken();
	if(CurTok != '(') Error("Expected a '(' to specify function to get pointer to.");
	getNextToken();
	if(CurTok != tok_id) Error("Expected function name to get pointer to.");
	std::string nm = IdStr;
	getNextToken();
	int et = LastIndex;
	if(CurTok != ')') Error("Expected ')'.");
	getNextToken(); // consume ')'
	ExprAST* res = new FuncRefExprAST(nm);
	exprLocation[res] = new FileLocation(st, et);
	return res;
}

// expression
// 	::= primary binoprhs
static ExprAST* ParseExpression(void){
	printf("Parsing an expression...\n");
	ExprAST* LHS = ParsePrimary();
	ExprAST* res = ParseBinOpRHS(0, LHS);
	return res;
}

// unaryexpr
//	::= unary_operator expression
static ExprAST* ParseUnaryExpr(void){
	int st = LastIndex;
	if(CurTok != tok_unary_op) Error("Expected a unary operator.");
	const std::string op = LastOp;
	getNextToken();
	ExprAST* on = ParseExpression(); // recursive grammars make life easier
	int et = LastIndex;
	ExprAST* res = (ExprAST*) new UnaryExprAST(op, on);
	exprLocation[res] = new FileLocation(st, et);
	return res;
}

// parenexpr ::= '(' expression ')'
// precond: current token is a '('
static ExprAST* ParseParenExpr(void){
	printf("Parsing a paranthesis expression...\n");
	int st = LastIndex;
	getNextToken(); // eat the '('
	ExprAST* V = ParseExpression();
	if(CurTok != ')') Error("Expected a ')'.");
	int et = LastIndex;
	getNextToken(); // consume ')'
	exprLocation[V] = new FileLocation(st, et);
	return V;
}

// identifierexpr
// 	::= identifier
//	::= identifier ('[' expression ']')*
// 	::= identifier '(' expression* ')'
// precond: current token is an ID
static ExprAST* ParseIdentifierExpr(void){
	printf("Parsing an identifier expression...\n");
	//int st = (LastIndex - IdStr.length() - 1);
	int st = LastLastIndex;
	std::string IdName = IdStr;
	int et = LastIndex;
	getNextToken();
	if(CurTok != '('){
		// Referencing a variable, and that's all.
		printf("Only a variable reference.\n");
		std::vector<ExprAST*> ind;
		while(CurTok == '['){
			getNextToken();
			ind.push_back(ParseExpression());
			if(CurTok != ']') Error("Expected ']'.");
			getNextToken();
		}
		VariableExprAST* ret = new VariableExprAST(IdName);
		ret->RegisterIndex(ind);
		if((CurTok == tok_op) && ((LastOp == "++") || (LastOp == "--"))){
			// UPDATEME/FIXME: fix & complete this
			// Handle post incr/decrement
			std::string op = (LastOp == "++") ? "+" : "-";
			ExprAST* bin_op = new BinaryExprAST(op, ret, new NumberExprAST(1));
			ret->RegisterPost(bin_op);
		}
		exprLocation[ret] = new FileLocation(st, et);
		return (ExprAST*) ret;
	}
	// Otherwise, it is a function call.
	getNextToken();
	std::vector<ExprAST*> Args;
	if(CurTok != ')'){
		while(true){
			ExprAST* Arg = ParseExpression();
			Args.push_back(Arg);
			if(CurTok == ')') break; // reached end of call
			if(CurTok != ','){
				// Error, should be either a ')' or a ',' after parsing the argument.
				Error("Expected a ')' or a ','.");
			}
			getNextToken();
		}
	}
	et = LastIndex;
	// Consume the ')'.
	getNextToken();
	ExprAST* res = new CallExprAST(IdName, Args);
	exprLocation[res] = new FileLocation(st, et);
	return res;
}

// castexpr
//	::= 'cast' '(' expr ',' typexpr ')'
static CastExprAST* ParseCastExpr(void){
	// TODO: Add more types of casts, make more extensible/flexible
	int st = (LastIndex - std::string("cast").length());
	printf("Parsing an explicit cast...\n");
	if(CurTok != tok_cast_to) Error("Expected an explicit cast.");
	getNextToken();
	if(CurTok != '(') Error("Expected a '('.");
	getNextToken();
	ExprAST* expr = (ExprAST*) ParseExpression();
	if(CurTok != ',') Error("Expected a ',' for specifying an input value to cast.");
	getNextToken();
	TypeExprAST* type = (TypeExprAST*) ParseTypeRef();
	int et = LastIndex;
	if(CurTok != ')') Error("Expected a ')'.");
	getNextToken();
	CastExprAST* res = new CastExprAST(type, expr);
	exprLocation[(ExprAST*) res] = new FileLocation(st, et);
	return res;
}

// stringexpr
//	::= '"' [*^\"] '"'
//	::= '"' (character NOT '"')* '"'
static StringExprAST* ParseStringExpr(void){
	int st = (LastIndex - (IdStr.length() + 3));
	printf("Parsing a string literal...\n");
	if(CurTok != tok_quoted_id) Error("Expected a string.");
	std::string val = IdStr;
	//printf("Val: |%s|\n", IdStr.c_str());
	//getchar();
	int et = LastIndex;
	getNextToken();
	StringExprAST* res = new StringExprAST(val);
	exprLocation[res] = new FileLocation(st, et);
	return res;
}	

// returnexpr
//	::= 'return' expr ';'
static ExprAST* ParseReturnExpr(void){
	printf("Parsing a 'return' statement...\n");
	int st = LastIndex;
	if(CurTok != tok_return) Error("Expected a 'return'.");
	getNextToken(); // consume the 'return'
	ExprAST* ret_val = NULL;
	/*
	switch(CurTok){
		case tok_id: ret_val = ParseIdentifierExpr(); break;
		case tok_num: ret_val = ParseNumberExpr(); break;
		case '(': ret_val = ParseParenExpr(); break;
		default: ErrorF("Unexpected token |%c| or |%d| after 'return'.", (char) CurTok, CurTok);
	}
	*/
	ret_val = ParseExpression();
	if(CurTok != ';') Error("Expected a semicolon.");
	int et = LastIndex;
	getNextToken(); // consume semicolon
	std::vector<ExprAST*> args;
	args.push_back(ret_val);
	printf("Parsed a 'return' statement.\n");
	ExprAST* res = new CallExprAST("return", args);
	exprLocation[res] = new FileLocation(st, et);
	return res;
}

// sizeofexpr
//	::= 'sizeof' '(' typeref ')'
//	::= 'sizeof' typeref
static ExprAST* ParseSizeOfExpr(void){
	// SizeOfExprAST(TypeExprAST* tp)
	int st = (LastIndex - IdStr.length());
	printf("Parsing a 'sizeof' expression...\n");
	if(CurTok != tok_size_of) Error("Expected 'sizeof'.");
	getNextToken();
	TypeExprAST* type = NULL;
	int et = LastIndex;
	if(CurTok == '('){ 
		getNextToken();
		type = (TypeExprAST*) ParseTypeRef();
		if(CurTok != ')') Error("Expected a closing ')' for 'sizeof' expression.");
		et = LastIndex;
		getNextToken();
	} else {
		type = (TypeExprAST*) ParseTypeRef();
		et = LastIndex;
	}
	printf("Parsed a 'sizeof' expression.\n");
	ExprAST* res = new SizeOfExprAST(type);
	exprLocation[res] = new FileLocation(st, et);
	return res;
}

// structexpr
//	::= 'struct' ':' typeref id ';'
static ExprAST* ParseStructExpr(void){
	// Working TODO:
	/*
	Make all declarations support commas in parsing to declare multiple vars - TODO
	Add a "sizeof" operator - TODO
	Fix/finish structs plus StructOffset function - DID? CHECKME
	Make a standard runtime library with llvm.global_ctors and dtors with CORRECT declarations for i32 printf, etc. - DOING
	Start adding some debugging information/metadata - TODO
	Fix '&' and ensure it works properly throughout all cases (structs, vars, arrays, etc.) - DID? CHECKME
	Allow programatically adding global ctors, dtors, and per-function, and operator overloading, and a full runtime - TODO
	Get a Linked List demo working - DONE
	*/
	int st = LastIndex;
	printf("Parsing a struct declaration...\n");
	if(CurTok != tok_struct) Error("Expected 'struct'.");
	getNextToken();
	if(CurTok != ':') Error("Expected ':'.");
	getNextToken();
	TypeExprAST* tp = (TypeExprAST*) ParseTypeRef();
	if(CurTok != tok_id) Error("Expected a variable name.");
	std::string name = IdStr;
	getNextToken();
	if(CurTok != ';') Error("Expected a ';' after struct insantiation.");
	int et = LastIndex;
	getNextToken();
	printf("Parsed a struct declaration.\n");
	ExprAST* res = new StructExprAST(name, tp);
	exprLocation[res] = new FileLocation(st, et);
	return res;
}

// classexpr
//	::= 'class' '{' (typeref id ';')* (definition)* '}' ';'
static ExprAST* ParseClassExpr(void){
	// ClassExprAST(const std::string& nm, const std::vector<std::tuple<TypeExprAST*, std::string> >& ivr, const std::vector<FunctionAST*>& mbs) 
	// : Name(nm), ivars(ivr), members(mbs)
	int st = LastIndex - IdStr.length() - 1;
	if(CurTok != tok_class) Error("Expected 'class'.");
	getNextToken();
	if(CurTok != tok_id) Error("Expected class name.");
	std::string name = IdStr;
	getNextToken();
	if(CurTok != '{') Error("Expected an opening '{' for class definition.");
	getNextToken();
	std::vector<std::tuple<TypeExprAST*, std::string> > ivars;
	while(CurTok != tok_func){
		TypeExprAST* type = (TypeExprAST*) ParseTypeRef();
		if(CurTok != tok_id) Error("Expected class instance variable name after type.");
		std::string on = IdStr;
		getNextToken();
		if(CurTok != ';') Error("Expected a ';' after class instance variable.");
		getNextToken();
		ivars.push_back(std::make_tuple(type, on));
	}
	std::vector<FunctionAST*> members;
	while(CurTok == tok_func){
		members.push_back(ParseDefinition());
	}
	if(CurTok != '}') Error("Expected a '}' after class.");
	getNextToken();
	int et = LastIndex;
	if(CurTok != ';') Error("Expected a ';' after class definition.");
	getNextToken();
	ExprAST* res = new ClassExprAST(name, ivars, members);
	exprLocation[res] = new FileLocation(st, et);
	return res;
}

// arrayexpr
// 	::= 'array' ':' typeref '=' '{' (expression [','])* '}' ';'
// 	::= 'array' ':' typeref id ('[' expression ']')* ';'
static ExprAST* ParseArrayExpr(void){
	/*
	dec array:double x = { 1, 2, 3, 4 }; // size inference
	dec array:int x2[25]; // declare array of ints of size 25
	*/
	/*
	std::string name; // array name
	TypeExprAST* type; // contained type
	ExprAST* size; // size of array
	std::vector<ExprAST*> initial; // for {...}-style declarations, the initial values of the array
	public:
		ArrayExprAST(std::string Name, TypeExprAST* Type) : name(Name), type(Type) {
			size = 0;
		}
		
		void SetSize(int Size){
			size = Size;
		}
		
		void RegisterInitial(std::vector<ExprAST*>& Initial){
			initial = Initial;
		}
		
		CGReturnType* Codegen(void);
	*/
	int st = LastIndex;
	printf("Parsing an array declaration...\n");
	if((IdStr != "array") || (CurTok != tok_id)) Error("Expected 'array'.");
	getNextToken();
	if(CurTok != ':') Error("Expected a colon.");
	getNextToken();
	TypeExprAST* type_ref = (TypeExprAST*) ParseTypeRef();
	if(CurTok != tok_id) Error("Expected array name.");
	std::string arr_name = IdStr;
	getNextToken();
	if(!(((CurTok == tok_op) && (LastOp == "=")) || (CurTok == '['))) Error("Unexpected token after array declaration.");
	if((CurTok == tok_op) && (LastOp == "=")){
		getNextToken();
		std::vector<ExprAST*> got;
		if(CurTok != '{') Error("Expected '{'.");
		getNextToken();
		while((CurTok != '}') && (CurTok != tok_eof)){
			got.push_back(ParseExpression());
			if(CurTok == ',') getNextToken();
		}
		if(CurTok == tok_eof) Error("Reached EOF while parsing array initialization via initializer list.");
		if(CurTok != '}') Error("Expected '}'.");
		getNextToken();
		if(CurTok != ';') Error("Expected a semicolon.");
		int et = LastIndex;
		getNextToken();
		ArrayExprAST* ret = new ArrayExprAST(arr_name, type_ref);
		ret->SetSize(new NumberExprAST((signed int) got.size()));
		ret->RegisterInitial(got);
		exprLocation[ret] = new FileLocation(st, et);
		return ret;
	} else if(CurTok == '['){
		//ExprAST* size = ParsePrimary();
		std::vector<ExprAST*> have;
		while(CurTok == '['){
			getNextToken();
			//if(CurTok != tok_num) Error("Expected a number.");
			ExprAST* size = ParseExpression();
			if(CurTok != ']') Error("Expected ']'.");
			getNextToken();
			have.push_back(size);
		}
		if(!have.size()) Error("Array must have at least one dimension.");
		if(CurTok != ';') Error("Expected a semicolon after array declaration.");
		int et = LastIndex;
		getNextToken();
		ArrayExprAST* ret = new ArrayExprAST(arr_name, type_ref);
		ret->SetSize(have);
		exprLocation[ret] = new FileLocation(st, et);
		return ret;
	} else assert(false && ("Should not get here!"));
	return NULL;
}

// newclassexpr
//	::= 'class' ':' typeref id [('(' expression [','] ')')* ] ';'
static ExprAST* ParseNewClassExpr(void){
	// NewClassExprAST(const std::string& nm, TypeExprAST* tp, std::vector<ExprAST*>& ct) : name(nm), type(tp), ctor_args(ct) {
	int st = LastLastIndex;
	if(CurTok != tok_class) Error("Expected 'class'.");
	getNextToken();
	if(CurTok != ':') Error("Expected a ':'.");
	getNextToken();
	TypeExprAST* tp = (TypeExprAST*) ParseTypeRef();
	if(CurTok != tok_id) Error("Expected a name for the instantiated class.");
	std::string name = IdStr;
	getNextToken();
	std::vector<ExprAST*> ctor_args;
	if(CurTok == '('){
		getNextToken();
		while(CurTok != ')'){
			ctor_args.push_back(ParseExpression());
			if(CurTok == ',') getNextToken();
		}
		getNextToken();
	}
	if(CurTok != ';') Error("Expected a ';' after class instantiation.");
	int et = LastIndex;
	getNextToken();
	NewClassExprAST* ret = new NewClassExprAST(name, tp, ctor_args);
	exprLocation[ret] = new FileLocation(st, et);
	return ret;
}

// decexpr
//	::= arrayexpr
//	::= structexpr
static ExprAST* ParseDecExpr(void){
	if(CurTok != tok_dec) Error("Expected a 'dec'.");
	getNextToken();
	if((CurTok == tok_id) && (IdStr == "array")) return ParseArrayExpr();
	else if(CurTok == tok_struct) return ParseStructExpr();
	else if(CurTok == tok_class) return ParseNewClassExpr();
	ErrorF(NULL, "Unexpected token |%c| or |%d| after 'dec'.", (char) CurTok, (int) CurTok);
	return NULL;
}

// structtyperef
//	::= 'struct' id '{' (typeref id ';')* '}' ';'
//	::= 'struct' id ';' // note: this is used for 'extern structs' --> LLVM "opaque" structure types
static ExprAST* ParseStructTypeRef(void){
	// StructTypeExprAST(const std::string& sn, std::vector<TypeExprAST*>& tp, std::vector<std::string>& nm)
	printf("Parsing a struct type declaration...\n");
	int st = LastIndex - IdStr.length();
	if(CurTok != tok_struct) Error("Expected 'struct'.");
	getNextToken(); // consume 'struct'
	if(CurTok != tok_id) Error("Expected a name for the struct.");
	std::string nm = IdStr;
	std::vector<TypeExprAST*> types;
	std::vector<std::string> names;
	getNextToken();
	if(CurTok != ';'){
		if(CurTok != '{') Error("Expected a '{'.");
		getNextToken();
		while(CurTok != '}'){
			types.push_back((TypeExprAST*) ParseTypeRef());
			if(CurTok != tok_id) Error("Expected a name after type for struct member.");
			names.push_back(IdStr);
			getNextToken();
			if(CurTok != ';') Error("Expected a ';' after struct member.");
			getNextToken();
		}
		getNextToken(); // consume '}'
		if(CurTok != ';') Error("Expected a ';' after struct declaration.");
	}
	int et = LastIndex;
	getNextToken();
	StructTypeExprAST* ret = new StructTypeExprAST(nm, types, names);
	exprLocation[ret] = new FileLocation(st, et);
	return (ExprAST*) ret;
}

// primary
// 	::= identifierexpr
// 	::= numberexpr
//	::= parenexpr
//	::= line
//	::= ifexpr
//	::= whileexpr
//	::= returnexpr
//	::= decexpr
//	::= stringexpr
//	::= forexpr
//	::= castexpr
//	::= unaryexpr
//	::= structtyperef // note: is technically allowed, but functions in the global namespace after the declaration
//	::= sizeofexpr
//	::= funcptrexpr
//	::= funcrefexpr
//	::= arrayptrexpr
static ExprAST* ParsePrimary(void){
	printf("Parsing a primary...\n");
	ExprAST* ret = NULL;
	switch(CurTok){
		case tok_id: ret = ParseIdentifierExpr(); break;
		case tok_num: ret = ParseNumberExpr(); break;
		case '(': ret = ParseParenExpr(); break;
		case tok_let: case tok_set: ret = ParseLine(); break;
		case tok_if: ret = ParseIfExpr(); break;
		case tok_while: ret = ParseWhileExpr(); break;
		case tok_return: ret = ParseReturnExpr(); break;
		case tok_dec: ret = ParseDecExpr(); break;
		case tok_quoted_id: ret = ParseStringExpr(); break;
		case tok_for: ret = ParseForExpr(); break;
		case tok_cast_to: ret = (ExprAST*) ParseCastExpr(); break;
		case tok_unary_op: ret = ParseUnaryExpr(); break;
		case tok_struct: ret = ParseStructTypeRef(); break;
		case tok_size_of: ret = ParseSizeOfExpr(); break;
		case tok_array_ptr: ret = ParseArrayPtrExpr(); break;
		case tok_func_ptr: ret = ParseFuncPtrExpr(); break;
		case tok_func_ptr_to: ret = ParseFuncRefExpr(); break;
		case tok_op:
			// Patch '&', '*', and '-'
			if((LastOp == "&") || (LastOp == "*") || (LastOp == "-")){
				CurTok = tok_unary_op;
				ret = ParseUnaryExpr();
				break;
			} // otherwise case label continues to default case
		default: ErrorF(NULL, "Unexpected token |%c| or |%d|.", (char) CurTok, CurTok);
	}
	printf("Parsed a primary.\n");
	return ret;
}

// typeref
//	::= id ('[' (numberexpr | <null>) ']')*
static ExprAST* ParseTypeRef(void){
	// Note: The ('[' ... ']')* part is intended for use in a prototype - NOT in a 'let <type>' setting or such.
	printf("Parsing a type reference...\n");
	if(CurTok == tok_func_ptr) return ParseFuncPtrExpr();
	if(CurTok == tok_array_ptr) return ParseArrayPtrExpr();
	int st = LastLastIndex;
	int et = LastIndex;
	if(CurTok != tok_id) Error("Expected a type name.");
	std::string type = IdStr; // type name
	getNextToken(); // consume type name
	if(CurTok == tok_num){ // for things like i32
		std::stringstream ss;
		ss << NumVal;
		type += ss.str();
		et = LastIndex;
		getNextToken(); // consume the number
	}
	int c = 0;
	if(typedefs.find(type) != typedefs.end()){
		// If this was a user-defined type
		std::tuple<std::string, int>& on = typedefs[type];
		type = std::get<0>(on); // get base type
		c += std::get<1>(on); // add by appropriate depth
	}
	while((CurTok == tok_op) && (LastOp == "*")){
		++c;
		printf("New depth: |%d|.\n", c);
		et = LastIndex;
		getNextToken(); // consume the '*'
	}
	while(CurTok == '['){
		// handle all of the array indices
		getNextToken();
		if(CurTok == tok_num) getNextToken();
		if(CurTok != ']') Error("Expected a ']' in array type reference.");
		et = LastIndex;
		getNextToken();
		++c; // an "array" can really just be represented as a pointer
	}
	printf("Type |%s| of depth |%d|.\n", type.c_str(), c);
	TypeExprAST* ret = new TypeExprAST(type);
	ret->SetDepth(c);
	exprLocation[ret] = new FileLocation(st, et);
	return ret;
}

// prototype
//	::= [('external' OR 'extern') '"' id '"'] 'fn' id [':' id] ['attributes' '[' (id [','])* ']' ] 'takes' '[' (typeref id ',')* ['...'] ']'
// Note: [...] denotes an optional field.
static ExprAST* ParsePrototype(void){
	int st = LastLastIndex;
	printf("Parsing a function prototype...\n");
	bool is_extern = false;
	std::string ExternStr = "";
	if(CurTok == tok_extern){
		is_extern = true;
		getNextToken();
		if(CurTok == tok_quoted_id){
			// TODO: Allow this to specify calling conv
			// Note: Is normally "C"
			ExternStr = IdStr;
			getNextToken();
		}
	}
	if(CurTok != tok_func) Error("Expected a function declaration.");
	getNextToken();
	if(CurTok != tok_id) Error("Expected a function name.");
	std::string name = IdStr; // function name
	getNextToken();
	TypeExprAST* ret_type = NULL; // return type, if/a
	if(CurTok == ':'){
		getNextToken();
		ret_type = (TypeExprAST*) ParseTypeRef();
	} else ret_type = new TypeExprAST("void");
	if((CurTok != tok_id) || ((IdStr != "takes") && (IdStr != "attributes"))) Error("Expected 'takes' or 'attributes'.");
	std::vector<std::string> attrs;
	if(IdStr == "attributes"){
		getNextToken();
		if(CurTok != '[') Error("Expected a '[' to specify attribute list.");
		getNextToken();
		while(CurTok != ']'){
			if((CurTok != tok_id) && (CurTok != tok_quoted_id)) Error("Expected an attribute string.");
			attrs.push_back(IdStr);
			getNextToken();
			if(CurTok == ',') getNextToken();
		}
		getNextToken(); // consume the ']'
		if((CurTok != tok_id) || (IdStr != "takes")) Error("Expected 'takes' after attribute list.");
	}
	getNextToken();
	if(CurTok != '[') Error("Expected '['.");
	getNextToken();
	std::vector<std::string> params; // parameter names
	std::vector<TypeExprAST*> types; // parameter types
	bool is_var_arg = false;
	while((CurTok != ']') && (CurTok != tok_eof)){
		if(CurTok != tok_elipsis){
			TypeExprAST* type_on = (TypeExprAST*) ParseTypeRef();
			if(CurTok != tok_id) Error("Expected a variable name.");
			std::string name_on = IdStr;
			getNextToken();
			params.push_back(name_on);
			types.push_back(type_on);
			if((CurTok != ',') && (CurTok != ']')) Error("Unexpected token.");
			if(CurTok == ',') getNextToken(); // consume the ','
		} else {
			is_var_arg = true;
			getNextToken(); // consume elipsis
			if(CurTok != ']') Error("A variable argument function must have the elipsis ('...') at the end."); // a '...' can ONLY be at the end
			if(!params.size()) Warn("A variable argument function should have at least one parameter to use as a starting point on stack.");
			break;
		}
	}
	if(CurTok == tok_eof) Error("Eached EOF while parsing function prototype.");
	if(CurTok != ']') Error("Expected ']'.");
	getNextToken(); // consume the ']'
	int et = LastIndex;
	if((CurTok != ';') && (CurTok != '{')) Error("Unexpected token after function declaration.");
	PrototypeAST* ret = new PrototypeAST(name, params, types, attrs);
	if(is_extern) ret->RegisterExtern(ExternStr);
	if(ret_type != NULL) ret->RegisterReturnType(ret_type);
	if(is_var_arg) ret->RegisterVarArg();
	printf("Parsed a function prototype for function |%s|.\n", name.c_str());
	exprLocation[ret] = new FileLocation(st, et);
	return (ExprAST*) ret;
}

// line
//	::= 'let' typeref id '=' expression [';']
// 	::= 'set' id '=' expression [';'] // UPDATE: deprecated
static LineExprAST* ParseLine(void){
	// UPDATE: Made the semicolon optional for 'for' loop compatibility
	int st = LastIndex;
	printf("Parsing a 'let' or a 'set'...\n");
	if((CurTok != tok_let) && (CurTok != tok_set)) Error("Expected 'let' or 'set'.");
	bool is_decl = (IdStr == "let") ? true : false;
	getNextToken(); // consume 'let'/'set'
	TypeExprAST* type = NULL;
	if(is_decl){
		type = (TypeExprAST*) ParseTypeRef();
	}
	if(CurTok != tok_id) Error("Expected a variable name.");
	std::string LHS = IdStr; // LHS/lvalue
	getNextToken();
	// TODO: Add (.) support for accessing struct members.
	if(((CurTok != '=') && (CurTok != '[')) || (CurTok == tok_op)){
		bool fl = false;
		if((CurTok == tok_op) && (LastOp != "=")) fl = true;
		if(CurTok != tok_op) fl = true;
		if(fl) Error("Expected a '='.");
	}
	std::vector<ExprAST*> indices;
	while(CurTok == '['){
		getNextToken();
		ExprAST* on = ParsePrimary(); // get array indice value provided
		if(CurTok != ']') Error("Expected a ']'.");
		getNextToken();
		indices.push_back(on);
	}
	getNextToken(); // consume the '='
	ExprAST* RHS = ParseExpression();
	int et = LastIndex;
	if(CurTok == ';') getNextToken(); // consume the semicolon if it exists - which in most cases, it should
	LineExprAST* ret = new LineExprAST(LHS, RHS);
	if(is_decl) ret->RegisterDeclaration(type);
	ret->RegisterIndices(indices);
	exprLocation[ret] = new FileLocation(st, et);
	return ret;
}

// definition ::= prototype '{' (expression)* '}'
// precond: should be on a function that is not external
static FunctionAST* ParseDefinition(void){
	printf("Parsing a function...\n");
	int st = LastIndex;
	PrototypeAST* Proto = (PrototypeAST*) ParsePrototype();
	if(CurTok == ';') Error("External functions must be declared as such.");
	if(CurTok != '{') Error("Unexpected token after function declaration - expected '{'.");
	getNextToken(); // consume the '{'
	std::vector<ExprAST*> lines;
	while((CurTok != '}') && (CurTok != tok_eof)){
		printf("Parsing a function body line...\n");
		lines.push_back(ParseExpression());
		if(CurTok == ';') getNextToken(); // consume the semicolon at the end of the line, if it exists
		printf("Parsed a function body line.\n");
	}
	if(CurTok == tok_eof) Error("Reached EOF while parsing a function definition.");
	if(CurTok != '}') Error("Expected '}' after parsing function body.");
	getNextToken(); // consume the '}'
	printf("Parsed a function.\n");
	ExprAST* ret = new FunctionAST(Proto, lines);
	int et = LastIndex;
	exprLocation[ret] = new FileLocation(st, et);
	return (FunctionAST*) ret;
}

// external ::= prototype
static ExprAST* ParseExtern(void){
	if(CurTok != tok_extern) Error("Expected 'external'.");
	return ParsePrototype();
}

// ifexpr 
//	::= 'if' parenexpr '{' (primary)* '}'
//	::= 'if' parenexpr expr [';']
//	::= 'if' parenexpr expr [';'] 'else' expr [';']
//	::= 'if' parenexpr expr [';'] 'else' ifexpr
//	::= 'if' parenexpr expr [';'] 'else' '{' (expr)* '}'
//	::= 'if' parenexpr '{' (expr)* '}' 'else' '{' (expr)* '}'
//	::= 'if' parenexpr '{' (expr)* '}' 'else' expr [';']
//	::= 'if' parenexpr '{' (expr)* '}' 'else' ifexpr
static ExprAST* ParseIfExpr(void){
	/*
	ExprAST* cond; // the condition to be evaluated
	std::vector<ExprAST*> if_true; // the "if true" or "then" branch
	std::vector<ExprAST*> if_false; // the "if false" or "else" branch
	public:
		IfExprAST(ExprAST* Cond, ExprAST* IfTrue, ExprAST* IfFalse) : cond(Cond) {
			if_true.push_back(IfTrue);
			if_false.push_back(IfFalse);
		}
		
		IfExprAST(ExprAST* Cond, std::vector<ExprAST*> IfTrue, std::vector<ExprAST*> IfFalse) : cond(Cond), if_true(IfTrue), if_false(IfFalse) {
			// not much... at all
		}
	*/
	printf("Parsing an 'if' statement...\n");
	if(CurTok != tok_if) Error("Expected an 'if'.");
	getNextToken();
	if(CurTok != '(') Error("Expected a '('.");
	ExprAST* cond_expr = ParseParenExpr(); // parse the condition
	if(CurTok != '{'){
		// If not a '{', must be a primary
		printf("Detected 'if' statement has primary-only first branch.\n");
		ExprAST* true_branch = ParseExpression();
		printf("Parsed 'if' statement primary-only true branch.\n");
		if(CurTok == ';') getNextToken(); // consume leftover semicolon if it exists
		if(CurTok != tok_else){
			printf("Parsed 'if'-only statement with no else branch."); 
			return new IfExprAST(cond_expr, true_branch, NULL); // e.g. if(cond) stmt;
		} else printf("Detected 'else' branch for primary-only true branch 'if' statement.\n");
		getNextToken(); // consume 'else'
		if((CurTok != tok_if) && (CurTok != '{')){
			ExprAST* false_branch = ParseExpression();
			if(CurTok == ';') getNextToken();
			return new IfExprAST(cond_expr, true_branch, false_branch); // e.g. if(cond) stmt; else stmt;
		} else if(CurTok == '{'){
			getNextToken(); // consume '{'
			std::vector<ExprAST*> lines;
			while((CurTok != '}') && (CurTok != tok_eof)){
				lines.push_back(ParseExpression());
				if(CurTok == ';') getNextToken();
				printf("Parsed an else body line.\n");
			}
			if(CurTok == tok_eof) Error("Reached EOF while parsing else body.");
			if(CurTok != '}') Error("Expected '}' after parsing else body.");
			getNextToken(); // consume '}'
			printf("Parsed an if-else statement.\n");
			std::vector<ExprAST*> true_vector;
			true_vector.push_back(true_branch);
			return new IfExprAST(cond_expr, true_vector, lines); // e.g. if(cond) stmt; else { stmts; }
		} else if(CurTok == tok_if){
			ExprAST* if_false = ParseIfExpr(); // recursive grammars rock
			return new IfExprAST(cond_expr, true_branch, if_false); // e.g. if(cond) stmt; else if(<cond...>) ...
		} else Error("Unexpected token - expecting 'else' branch.");
	}
	getNextToken(); // consume '{'
	std::vector<ExprAST*> true_branch;
	std::vector<ExprAST*> false_branch;
	while((CurTok != '}') && (CurTok != tok_eof)){
		true_branch.push_back(ParseExpression());
		if(CurTok == ';') getNextToken();
		printf("Parsed an if body line.\n");
	}
	if(CurTok == tok_eof) Error("Reached EOF while parsing if body.");
	if(CurTok != '}') Error("Expected '}' after parsing if body.");
	getNextToken(); // consume '}'
	if(CurTok != tok_else) return new IfExprAST(cond_expr, true_branch, false_branch); // e.g. if(cond){ stmts; }
	getNextToken(); // consume 'else'
	if((CurTok != tok_if) && (CurTok != '{')){
		false_branch.push_back(ParseExpression());
		if(CurTok == ';') getNextToken();
		return new IfExprAST(cond_expr, true_branch, false_branch); // e.g. if(cond){ stmts; } else stmt;
	} else if(CurTok == '{'){
		getNextToken(); // consume '{'
		while((CurTok != '}') && (CurTok != tok_eof)){
			false_branch.push_back(ParseExpression());
			if(CurTok == ';') getNextToken();
			printf("Parsed an else body line.\n");
		}
		if(CurTok == tok_eof) Error("Reached EOF while parsing else body.");
		if(CurTok != '}') Error("Expected '}' after parsing else body.");
		getNextToken(); // consume '}'
		printf("Parsed an if-else statement.\n");
		return new IfExprAST(cond_expr, true_branch, false_branch); // e.g. if(cond){ stmts; } else { stmts; }
	} else if(CurTok == tok_if){
		false_branch.push_back(ParseIfExpr()); //  recursive grammar
		return new IfExprAST(cond_expr, true_branch, false_branch); // e.g. if(cond){ stmts; } else if(<cond...>) ...
	} else Error("Unexpected token - expecting 'else' branch.");
	return NULL;
}

// whileexpr
//	::= 'while' parenexpr expr [';']
//	::= 'while' parenexpr '{' (expr)* '}'
static ExprAST* ParseWhileExpr(void){
	/*
	ExprAST* cond; // the condition to be evaluated at the start of every loop
	std::vector<ExprAST*> body; // the body of the while loop
	public:
		WhileExprAST(ExprAST* Cond, ExprAST* Body) : cond(Cond) {
			body.push_back(Body);
		}
		
		WhileExprAST(ExprAST* Cond, std::vector<ExprAST*> Body) : cond(Cond), Body(body) {
			// nothing - really!
		}
	*/
	printf("Parsing a 'while' loop...\n");
	if(CurTok != tok_while) Error("Expected a 'while'.");
	getNextToken(); // consume the 'while'
	ExprAST* cond_v = ParseParenExpr();
	if(CurTok != '{'){
		ExprAST* if_true = ParseExpression();
		if(CurTok == ';') getNextToken();
		return new WhileExprAST(cond_v, if_true); // e.g. while(cond) stmt;
	}
	getNextToken(); // consume '{'
	std::vector<ExprAST*> body;
	while((CurTok != '}') && (CurTok != tok_eof)){
		body.push_back(ParseExpression());
		if(CurTok == ';') getNextToken();
	}
	if(CurTok == tok_eof) Error("Reached EOF while parsing 'while' loop body.");
	if(CurTok != '}') Error("Expected a '}'.");
	getNextToken(); // consume the '}'
	printf("Parsed a 'while' loop.\n");
	return new WhileExprAST(cond_v, body);
}

// forexpr
//	::= 'for' '(' expr [';'] expr [';'] expr ')' expr ';'
//	::= 'for' '(' expr [';'] expr [';'] expr ')' '{' (expr)* '}'
static ExprAST* ParseForExpr(void){
	/*
	ExprAST* init; // the "initialization" part of the loop
	ExprAST* cond; // the condition to be evaluated every time the loop runs
	ExprAST* incr; // the "increment" statement or such
	std::vector<ExprAST*> body; // the body of the for loop
	public:
		ForExprAST(ExprAST* Init, ExprAST* Cond, ExprAST* Incr) : init(Init), cond(Cond), incr(Incr) {
			// nothing = win
		}
		
		void RegisterBody(ExprAST* Body){
			body.push_back(Body);
		}
		
		void RegisterBody(std::vector<ExprAST*> Body){
			body = Body;
		}
	*/
	printf("Parsing a 'for' loop...\n");
	if(CurTok != tok_for) Error("Expected a 'for'.");
	getNextToken();
	if(CurTok != '(') Error("Expected '('.");
	getNextToken();
	printf("F1\n");
	ExprAST* initial = (CurTok != ';') ? ParseExpression() : NULL; // allow for(; <...>)
	if(CurTok == ';') getNextToken();
	printf("F2\n");
	ExprAST* condition = (CurTok != ';') ? ParseExpression() : NULL; // allow for(<...>;;<...>)
	if(CurTok == ';') getNextToken();
	printf("F3\n");
	ExprAST* increment = (CurTok != ')') ? ParseExpression() : NULL; // allow no increments
	if(CurTok == ';') getNextToken();
	if(CurTok != ')') Error("Expected a ')'.");
	getNextToken();
	printf("F4\n");
	ForExprAST* ret = new ForExprAST(initial, condition, increment);
	if(CurTok != '{'){
		ExprAST* branch = ParseExpression();
		if(CurTok == ';') getNextToken();
		ret->RegisterBody(branch);
		return (ExprAST*) ret;
	}
	getNextToken();
	std::vector<ExprAST*> branch;
	while((CurTok != '}') && (CurTok != tok_eof)){
		branch.push_back(ParseExpression());
		if(CurTok == ';') getNextToken();
	}
	if(CurTok == tok_eof) Error("Reached EOF while parsing 'for' loop body.");
	getNextToken(); // consume '}'
	ret->RegisterBody(branch);
	return (ExprAST*) ret;
}

// Code Generation: //

struct VarSymbol;
struct FuncSymbol;

static Module* mod;
static IRBuilder<> Builder(getGlobalContext());
static FunctionPassManager* TheFPM;
//static ExecutionEngine* TheExecutionEngine;
static std::map<std::string, VarSymbol*> VarTable; // variable symbol table
static std::vector<std::map<std::string, VarSymbol*> > VarTableStack; // symbol table "stack" --> used for scoping
static std::map<std::string, std::vector<FuncSymbol*> > FuncTable; // function symbol table with support for overloading
static std::vector<std::map<std::string, std::vector<FuncSymbol*> > > FuncTableStack; // function symbol table "stack" --> used for namespace nesting (e.g. in classes)
static std::map<std::string, Type*> TypeTable; // table for registered struct types, etc.
static std::map<StructType*, std::vector<std::tuple<std::string, Type*> > > StructMemberTable; // struct member table for registered structs
static std::map<StructType*, std::vector<std::tuple<std::string, FuncSymbol*> > > ClassMemberTable; // class member table for registered classes

static FuncSymbol* cur_func = NULL; // the name of the current function that code is being generated for
static bool ShouldOptimize = true; // whether to optimize or not
static bool EmittingForClass = false; // whether emitting code for a class member currently or not (will not be set if emitting for ctor/dtor)
static Type* ClassPtrType = NULL; // type of class ptr for current class
static Value* ClassEmittingPtr = NULL; // when emitting for a class, the implicit class pointer is set for abstracting away ivar details
static bool EmittingClassCtor = false; // whether emitting for a class ctor

VarSymbol* LookupVar(std::string var_name){
	if(VarTable.find(var_name) != VarTable.end()) return VarTable[var_name]; // look at current first
	for(std::vector<std::map<std::string, VarSymbol*> >::reverse_iterator it = VarTableStack.rbegin(); it != VarTableStack.rend(); it++){
		// Since it acts as a stack, look at most recently added first.
		std::map<std::string, VarSymbol*>& on = *it;
		if(on.find(var_name) != on.end()) return on[var_name];
	}
	return NULL; // not found
}

void PushVarScope(void){
	// New variable sub-scope --> pushes existing on stack
	VarTableStack.push_back(VarTable);
	VarTable.clear();
}

void PopVarScope(void){
	// Restore last variable scope, discard existing one
	VarTable = VarTableStack.back();
	VarTableStack.pop_back();
}

std::vector<FuncSymbol*> LookupFunc(std::string func_name){
	std::vector<FuncSymbol*> ret;
	if(FuncTable.find(func_name) != FuncTable.end()){
		// First, add in current scope's possibilities
		std::vector<FuncSymbol*>& on = FuncTable[func_name];
		ret.reserve(on.size());
		ret.insert(ret.end(), on.begin(), on.end());
	}
	for(auto it = FuncTableStack.rbegin(); it != FuncTableStack.rend(); it++){
		std::map<std::string, std::vector<FuncSymbol*> >& on = *it;
		if(on.find(func_name) != on.end()){
			std::vector<FuncSymbol*>& on_v = on[func_name];
			ret.reserve(ret.size() + on.size());
			ret.insert(ret.end(), on_v.begin(), on_v.end());
		}
	}
	return ret;
}

void PushFuncScope(void){
	// New function sub-scope --> pushes existing on stack
	FuncTableStack.push_back(FuncTable);
	FuncTable.clear();
}

void PopFuncScope(void){
	// Restore last function scope, discard existing one
	FuncTable = FuncTableStack.back();
	FuncTableStack.pop_back();
}

Value* ValueFor(CGReturnType* cg_ret){
	// Get the value for a return type.
	// If it is an AllocaInst*, returns a LoadInst*.
	if(!cg_ret->is_alloca) return cg_ret->val;
	return Builder.CreateLoad(cg_ret->val, "loadtmp");
}

bool AreEqualTypes(llvm::Type* t1, llvm::Type* t2){
	if(!t1 || !t2) Error("Passed a NULL type.");
	if(t1->isPointerTy() || t2->isPointerTy()){
		// if either is a pointer type
		if(!t1->isPointerTy() || !t2->isPointerTy()) return false; // have to both be pointers then
		return (AreEqualTypes(t1->getPointerElementType(), t2->getPointerElementType())); // a bit of recursive magic
	}
	if(t1->getTypeID() == t2->getTypeID()){
		if(t1->getTypeID() != 10) return true; // if they are equal but NOT integral types, return true
	} else return false;
	// if they are integral types, then check their bit widths to determine equality
	return (t1->getIntegerBitWidth() == t2->getIntegerBitWidth());
}

bool CanCastTo(llvm::Type* from, llvm::Type* to){
	Type* orig = from;
	unsigned int orig_depth = 0;
	while(orig->isPointerTy()){
		++orig_depth;
		orig = orig->getPointerElementType();
	}
	if(!orig->isArrayTy()) return (CastInst::isCastable(from, to));
	else if(orig->isArrayTy()){
		// then add up all layers of indirection to contained element type and see
		// if it can be matched to the 'to' type
		// note: the levels of pointer indirection (e.g. # of *'s) and contained type are compared to check for castability
		Type* arr_orig = orig;
		unsigned int depth = orig_depth;
		while(arr_orig->isArrayTy()){
			++depth; // another layer of indirection
			arr_orig = arr_orig->getArrayElementType();
		}
		while(arr_orig->isPointerTy()){
			arr_orig = arr_orig->getPointerElementType();
			++depth; // yet another layer of indirection
		} // 'arr_orig' now contains final contained type
		unsigned int ot_depth = 0; // depth of 'to' type
		Type* ot_orig = to;
		while(ot_orig->isPointerTy() || ot_orig->isArrayTy()){
			++ot_depth;
			if(ot_orig->isPointerTy()) ot_orig = ot_orig->getArrayElementType();
			else if(ot_orig->isArrayTy()) ot_orig->getArrayElementType();
		}
		printf("Array cast check: %u vs %u depth.\n", depth, ot_depth);
		if((depth != ot_depth) || !AreEqualTypes(arr_orig, ot_orig)) return false; // contained types MUST be equivalent
		return true;
	}
	return false; // not castable by default
}

inline bool CanCastTo(llvm::Value* from, llvm::Type* to){
	return (CanCastTo(from->getType(), to));
}

inline bool CanCastTo(llvm::Value* from, llvm::Value* to){
	return (CanCastTo(from->getType(), to->getType()));
}

bool CanSafelyCastTo(llvm::Value* from, llvm::Type* to){
	// This is similar to CanCastTo, except this takes into account type safety checking rules //
	// precond: types are NOT already equal
	if(!CanCastTo(from, to)) return false; // if there is not even a cast available, then not happening
	llvm::Type* t1 = from->getType();
	llvm::Type* t2 = to;
	assert(!AreEqualTypes(t1, t2));
	int tid1 = (signed int) t1->getTypeID();
	int tid2 = (signed int) t2->getTypeID();
	assert((tid1 && tid2) && ("No void types allowed!"));
	assert((tid1 != 11) && (tid2 != 11) && ("No function types allowed!"));
	assert((tid1 != 8) && (tid2 != 8) && ("No metadata types allowed!"));
	assert((tid1 != 7) && (tid2 != 7) && ("No label types allowed!"));
	if(((tid1 == 10) || (tid1 <= 6)) && ((tid2 == 10) || (tid2 <= 6))){
		// Allow all floating-point/integral casts to each other
		return true;
	}
	if(tid1 == tid2){
		// Handle this case
		if(tid1 == 14){
			// Pointers must be explicitly cast to each other
			return false;
		}
		return true;
	} else {
		if(t1->isArrayTy() && t2->isPointerTy()) return true; // allow the array to pointer cast (explicitly checked for in CanCastTo)
		return false; // must be something like a struct to an array or such
	}
}

int ShouldCastWhich(llvm::Value* p1, llvm::Value* p2){
	// Returns 0 if should cast p1 to p2's type, or 1 if should cast p2 to p1's type.
	// Returns -1 if neither can be cast to each other's type.
	// Note: Primarily for use with integer promotion and such (should downcast or upcast/promote)
	// precond: Type ID's of p1's type and p2's type should NOT be equal.
	/**
	* Casts Allowed:
	* All integral and floating-point casts to any of each other's type.
	**/
	llvm::Type* t1 = p1->getType();
	llvm::Type* t2 = p2->getType();
	assert(!AreEqualTypes(t1, t2)); // assert precond
	if((!CanCastTo(t1, t2)) && (!CanCastTo(t2, t1))) return -1;
	int tid1 = (signed int) t1->getTypeID();
	int tid2 = (signed int) t2->getTypeID();
	assert((tid1 && tid2) && ("No void types allowed!")); // no void (0) types please
	if(tid1 == tid2){
		return (CanCastTo(t1, t2)) ? 0 : 1;
	}
	if(tid1 == 10){
		// if p1 is an integer, and p2 is not
		// then only cast if p2 is some floating-point type
		if(tid2 <= 6) return 0;
	} else if(tid2 == 10){
		// if p2 is an integer, and p1 is not
		// then only cast if p1 is some floating-point type
		if(tid1 <= 6) return 1;
	} else if((tid1 <= 6) && (tid2 <= 6)){
		// Both are floating-point types, but of different sizes
		// prefer upcasts in size
		if(tid1 > tid2) return 1; // if t1 is bigger, cast t2 to t1
		return 0; // or vica versa
	}
	if((tid1 == 14) || (tid2 == 14)){
		if((tid1 != 14) || (tid2 != 14)) return -1; // no pointer to int, etc. casts allowed implicitly
	}
	if(!CanCastTo(t1, t2)) return 1; // can't cast p1 to p2, so should cast p2 to p1
	if(!CanCastTo(t2, t1)) return 0; // and vica versa
	return 1; // by default, cast second one then
}

std::tuple<int, Type*> GetStructOffsetFor(StructType* struct_type, std::string member){
	// Returns offset [0 = first, etc.] and Type of a given struct member given struct type and member name.
	// std::map<StructType*, std::vector<std::tuple<std::string, Type*> > > StructMemberTable
	int off = -1;
	Type* type = NULL;
	if(StructMemberTable.find(struct_type) == StructMemberTable.end()) Error("Could not find struct member table entry for given struct type.");
	std::vector<std::tuple<std::string, Type* > >& on = StructMemberTable[struct_type];
	assert(on.size());
	for(unsigned int i = 0; i < on.size(); i++){
		std::tuple<std::string, Type*>& on_t = on[i];
		assert(std::get<1>(on_t) == struct_type->getElementType(i));
		if(std::get<0>(on_t) == member){
			printf("Found member |%s| at offset |%u|.\n", member.c_str(), i);
			off = (signed int) i;
			type = std::get<1>(on_t);
			break;
		}
	}
	if(!type || (off == -1)) Error("Could not find struct member in given struct type.");
	return std::make_tuple(off, type);
}

Value* CastTo(Value* from, llvm::Type* to, bool src_signed = true, bool dest_signed = true){
	assert(CanCastTo(from, to));
	if(((signed int) from->getType()->getTypeID() == 10) && ((signed int) to->getTypeID() <= 6)){
		Warn("Casting from a floating-point value to an integral value truncates the decimal point.");
	}
	if(from->getType()->getTypeID() == 13){ // array cast to pointer
		// Then use a carefully crafted GEP to convert to a pointer of the correct indirection level
		from->dump();
		assert(isa<LoadInst>(from) && ("Array should be loaded!"));
		from = ((LoadInst*) from)->getPointerOperand();
		std::vector<Value*> idx;
		idx.push_back(ConstantInt::get(mod->getContext(), APInt(64, 0))); // step over
		idx.push_back(ConstantInt::get(mod->getContext(), APInt(64, 0)));
		printf("Creating array decay...\n");
		Value* ret = Builder.CreateInBoundsGEP(from, idx, "geparrcasttmp");
		printf("Created array decay!\n");
		return ret;
	}
	Instruction::CastOps opcode = CastInst::getCastOpcode(from, src_signed, to, dest_signed);
	return Builder.CreateCast(opcode, from, to, "castinst");
}

void CastAsNecessary(llvm::Value*& p1, llvm::Value*& p2, bool src_signed = true, bool dest_signed = true){
	// Updates either p1 or p2 -- up to caller to update references and/or save old value.
	int shd = ShouldCastWhich(p1, p2);
	if(!shd){
		// Cast p1 to p2
		p1 = CastTo(p1, p2->getType(), src_signed, dest_signed);
	} else if(shd == 1){
		// Cast p2 to p1
		p2 = CastTo(p2, p1->getType(), src_signed, dest_signed);
	} // if shld == -1, nothing is done
}

// CGReturnType(Value* vl, Type* tp, bool alloca, bool is_func)

CGReturnType* TypeExprAST::Codegen(void){
	llvm::Type* ret = NULL;
	printf("Generating type code for |%s|...\n", Type.c_str());
	//bool is_integral = (Type[0] == 'i');
	if(Type == "f64") ret = Type::getDoubleTy(mod->getContext());
	else if(Type == "f16") ret = Type::getHalfTy(mod->getContext());
	else if(Type == "f32") ret = Type::getFloatTy(mod->getContext());
	else if(Type == "f80") ret = Type::getX86_FP80Ty(mod->getContext());
	else if(Type == "f128") ret = Type::getFP128Ty(mod->getContext());
	else if(Type == "i1") ret = (llvm::Type*) Type::getInt1Ty(mod->getContext());
	else if(Type == "i8") ret = (llvm::Type*) Type::getInt8Ty(mod->getContext());
	else if(Type == "i16") ret = (llvm::Type*) Type::getInt16Ty(mod->getContext());
	else if(Type == "i32") ret = (llvm::Type*) Type::getInt32Ty(mod->getContext());
	else if(Type == "i64") ret = (llvm::Type*) Type::getInt64Ty(mod->getContext());
	else if(Type == "void"){ 
		if(!depth) ret = Type::getVoidTy(mod->getContext());
		else ret = (llvm::Type*) Type::getInt8Ty(mod->getContext()); // to allow void*, void**, etc.
	} else if(Type[0] == 'i'){
		// arbitrary bit-width integral values
		std::string rest = Type.substr(1);
		int num = atoi(rest.c_str());
		if(num <= 0) ErrorF(this, "No 0-bit-width or negative-bit-width integral types allowed (given %d in '%s')!", num, Type.c_str());
		ret = (llvm::Type*) IntegerType::get(mod->getContext(), (unsigned int) num);
	} else if(TypeTable.find(Type) != TypeTable.end()){
		ret = TypeTable.at(Type);
		printf("Found |%p| with ID |%d| in type table.\n", ret, ret->getTypeID());
	}
	for(int i = 0; i < depth; i++){
		if(!ret) break;
		ret = (llvm::Type*) PointerType::get(ret, 0);
	}
	if(!ret) Error("Unrecognized type '" + Type + "'.", this);
	printf("Generated type code.\n");
	return new CGReturnType((Value*) ret, ret, false, false);
}

CGReturnType* FuncPtrExprAST::Codegen(void){
	// std::vector<TypeExprAST*> types
	// TODO: Add vararg function pointer types
	if(!types.size()) Error("A function pointer must specify a return type at least.", this);
	std::vector<Type*> tp;
	Type* return_type = types[0]->Codegen()->type;
	assert(FunctionType::isValidReturnType(return_type));
	for(unsigned int i = 1; i < types.size(); i++){
		CGReturnType* tph = types[i]->Codegen();
		tp.push_back(tph->type);
		assert(FunctionType::isValidArgumentType(tph->type));
	}
	Type* ret = (Type*) FunctionType::get(return_type, tp, false); // false = isVarArg
	ret = ret->getPointerTo(0);
	return new CGReturnType((Value*) ret, ret, false, false);
}

CGReturnType* ArrayPtrExprAST::Codegen(void){
	// TypeExprAST* type, ExprAST* size
	Type* tp = type->Codegen()->type;
	Value* szh = size->Codegen()->val;
	if(!isa<ConstantInt>(szh)) Error("Need a constant integral value to specify array size type.", this);
	ConstantInt* sz = cast<ConstantInt>(szh);
	Type* ret = ArrayType::get(tp, sz->getZExtValue());
	return new CGReturnType((Value*) ret, ret, false, false);
}

CGReturnType* FuncRefExprAST::Codegen(void){
	// std::string name
	// TODO: Disambiguate between different overloads of same function
	Function* func = mod->getFunction(name);
	if(!func) Error("Could not find function '" + name + "'.");
	return new CGReturnType((Value*) func, (Type*) func->getFunctionType(), false, false);
}

CGReturnType* StructTypeExprAST::Codegen(void){
	// StructTypeExprAST(const std::string& sn, std::vector<TypeExprAST*>& tp, std::vector<std::string>& nm)
	// struct_name, types, names
	// std::map<std::string, std::vector<std::tuple<std::string, Type*> > > StructMemberTable
	StructType* ret = StructType::create(mod->getContext(), ("struct." + struct_name));
	TypeTable[struct_name] = (Type*) ret; // so that forward references/recursive types can be resolved (e.g. for linked lists)
	assert(ret->hasName());
	assert(types.size() == names.size());
	if(!types.size()){
		// If no body was provided, it was an "extern" declaration of a struct (e.g. an LLVM opaque type).
		return new CGReturnType((Value*) ret, ret, false, false);
	}
	std::vector<Type*> tp;
	std::vector<std::tuple<std::string, Type*> > tbl;
	unsigned int on_c = 0;
	for(TypeExprAST* on_h : types){
		CGReturnType* onh = on_h->Codegen();
		assert(onh->val);
		Type* on = (Type*) onh->val;
		if(!StructType::isValidElementType(on)) Error("Element '" + names[on_c] + "' cannot be an element type in a struct.", this);
		tp.push_back(on);
		tbl.push_back(std::make_tuple(names[on_c], on));
		++on_c;
	}
	ret->setBody(tp);
	assert(!ret->isOpaque() && !ret->isPacked());
	printf("Struct type dump:\n");
	ret->dump();
	printf("\n");
	assert(StructMemberTable.find(ret) == StructMemberTable.end());
	StructMemberTable[ret] = tbl;
	return new CGReturnType((Value*) ret, ret, false, false);
}

CGReturnType* NumberExprAST::Codegen(void){
	Value* ret = NULL; // e.g. ConstantFP::get(mod->getContext(), APFloat(val))
	Type* type = NULL; // e.g. Type::getDoubleTy(mod->getContext())
	// Try to store the value in the "smallest" type possible.
	// FIXME: for now, the only types considered are i32 and f64
	if(dec_point){
		ret = ConstantFP::get(mod->getContext(), APFloat(val));
		type = Type::getDoubleTy(mod->getContext());
	} else {
		type = Type::getInt32Ty(mod->getContext()); // i32 - 4-byte integral value
		ret = ConstantInt::getSigned((IntegerType*) type, (signed int) val);
	}
	return new CGReturnType(ret, type, false, false);
}

CGReturnType* VariableExprAST::Codegen(void){
	// Note: Any ID's will be parsed as a VariableExprAST, so constants are handled here as well.
	Value* const_ret = NULL;
	if(name == "true"){
		const_ret = ConstantInt::getTrue(mod->getContext());
	} else if(name == "false"){
		const_ret = ConstantInt::getFalse(mod->getContext());
	} else if(name == "NULL"){
		const_ret = Constant::getNullValue((Type::getInt8Ty(mod->getContext()))->getPointerTo(0)); // NULL is by default a char*
	}
	if(const_ret) return new CGReturnType(const_ret, const_ret->getType(), false, false);
	printf("Generating code for a variable reference for variable |%s|...\n", name.c_str());
	VarSymbol* symbol = LookupVar(name);
	const std::string nm = name;
	if(!symbol) Error("Undeclared variable '" + name + "' referenced.", this);
	llvm::Type* type = symbol->type;
	if(!indices.size()){
		// not an array reference, just a regular one
		AllocaInst* val = (AllocaInst*) symbol->val;
		LoadInst* load = Builder.CreateLoad(val, "loadtmp");
		printf("Generated code for a variable reference.\n");
		return new CGReturnType(load, type, false, false);
	} else {
		AllocaInst* arr_ptr = (AllocaInst*) symbol->val;
		LoadInst* arr = (LoadInst*) arr_ptr;
		std::string name = arr_ptr->getName();
		// convention: if it has a ".ptr" at end, load it //
		bool loaded = false;
		if(name.length() > 4){
			size_t pos = name.find(".ptr");
			if(pos != std::string::npos){ 
				arr = Builder.CreateLoad(arr_ptr, "loadtmp");
				loaded = true;
			}
		}
		/*
		if(!loaded && (arr->getType()->getTypeID() == 14)){
			arr = Builder.CreateLoad(arr_ptr, "loadtmp");
			loaded = true;
		}
		*/
		Type* pointed_type_orig = arr->getType();
		unsigned int type_depth = 0;
		while(pointed_type_orig->getTypeID() == 14){
			++type_depth;
			pointed_type_orig = pointed_type_orig->getPointerElementType();
		}
		assert(pointed_type_orig->getTypeID() != 14);
		std::vector<Value*> inds;
		if(!loaded){
			printf("Not loaded for |%s|, step over added.\n", name.c_str());
			inds.push_back(ConstantInt::get(mod->getContext(), APInt(64, 0))); // step-over index for a "static" array
		}
		for(std::vector<ExprAST*>::iterator it = indices.begin(); it != indices.end(); it++){
			ExprAST* on = *it;
			CGReturnType* genh = on->Codegen();
			if(genh->val->getType()->getTypeID() != 10) Error("Array indices must be integers.");
			inds.push_back(CastTo(genh->val, Type::getInt64Ty(mod->getContext())));
		}
		if(type_depth){
			// check if something like int**
			int tid = pointed_type_orig->getTypeID();
			pointed_type_orig->dump();
			if((tid < 6) || ((tid >= 10) && (tid != 11) && (tid != 13))){
				printf("Using pointer array addressing.\n");
				// now use the "correct" way to use inbounds GEP for this
				Value* ret = arr;
				if(isa<AllocaInst>(ret)){
					ret = Builder.CreateLoad(ret, "ptrarrloadtmp");
				}
				unsigned int on = (loaded) ? 0 : 1; // b/c if(!loaded) then step over index was added
				for(unsigned int i = 0; i < indices.size(); i++){ // loop as many times as there are indices
					ret = Builder.CreateLoad(Builder.CreateInBoundsGEP(ret, inds[on++], "ptrarrgeptmp"), "ptrarrloadtmp");
				}
				return new CGReturnType(ret, ret->getType(), false, false);
			}
		}
		//Builder.GetInsertBlock()->getParent()->dump();
		//getchar();
		//arr->getType()->dump();
		//arr->dump();
		printf("Arr dump:\n");
		arr->dump();
		for(unsigned int i = 0; i < inds.size(); i++){
			printf("ind #%d: \n", i);
			inds[i]->getType()->dump();
			printf("end ind\n");
		}
		Type* rg = GetElementPtrInst::getIndexedType(arr->getType(), inds);
		printf("arr name: %s\n", nm.c_str());
		assert(rg);
		//Type* rg = GetElementPtrInst::getGEPReturnType(arr, inds);
		printf("rg: \n");
		rg->dump();
		printf("\nend rg\n");
		Value* gep = Builder.CreateInBoundsGEP(arr, inds, "arrloadtmp");
		LoadInst* load = Builder.CreateLoad(gep, "loadtmp");
		printf("Ret var type:\n");
		load->getType()->dump();
		printf("\n");
		return new CGReturnType(load, load->getType(), false, false);
	}
}

CGReturnType* SizeOfExprAST::Codegen(void){
	printf("Generating code for a 'sizeof' expression...\n");
	Type* tp = type->Codegen()->type;
	assert(tp);
	tp = tp->getPointerTo();
	printf("0.5\n");
	Value* null_val = Constant::getNullValue(tp);
	Value* int_1 =  ConstantInt::get(mod->getContext(), APInt(32, 1));
	Value* gep = Builder.CreateGEP(null_val, int_1, "sizeofgeptmp");
	printf("1\n");
	Value* ret = CastTo(gep, (llvm::Type*) Type::getInt64Ty(mod->getContext()), false, false); // false, false = src/dest signed
	ret->dump();
	return new CGReturnType(ret, ret->getType(), false, false);
}

CGReturnType* BinaryExprAST::Codegen(void){
	// TODO: Add start and end information for this one in exprLocation (in parsing mainly)
	printf("Generating code for a binary expression...\n");
	if((exprLocation.find(RHS) != exprLocation.end()) && (exprLocation.find(LHS) != exprLocation.end())){
		// Dynamically add location information
		exprLocation[this] = new FileLocation(exprLocation[LHS]->st, exprLocation[RHS]->et);
	}
	CGReturnType* Lh = LHS->Codegen();
	Value* L = ValueFor(Lh);
	if((Op == ".") || (Op == "->")){
		if(Op == "->"){
			L = Builder.CreateLoad(L, "selloadtmp");
		}
		if(!isa<StructType>(L->getType())) Error("A selection operator can only be used on a structure or a class.", this);
		if(isa<VariableExprAST>(RHS)){
			// Handle a struct member reference.
			// Note: Done before RHS code generation since '.' is used like (struct.member)
			// and emitting code for 'member' would result in an error since it is (probably)
			// not a variable.
			Value* val = L;
			val->dump();
			assert(isa<LoadInst>(val));
			val = (Value*) ((LoadInst*) val)->getPointerOperand();
			val->dump();
			//assert(isa<AllocaInst>(val));
			// std::tuple<int, Type*> GetStructOffsetFor(StructType* struct_type, std::string member)
			VariableExprAST* RHS_casted = (VariableExprAST*) RHS;
			std::tuple<int, Type*> off = GetStructOffsetFor((StructType*) L->getType(), RHS_casted->GetName());
			std::vector<Value*> idx;
			idx.push_back(ConstantInt::get(mod->getContext(), APInt(32, 0)));
			idx.push_back(ConstantInt::get(mod->getContext(), APInt(32, std::get<0>(off))));
			Type* ret_type = GetElementPtrInst::getIndexedType(val->getType(), idx);
			ret_type->dump();
			assert(ret_type && (ret_type->getTypeID() == std::get<1>(off)->getTypeID()));
			Value* gep = Builder.CreateInBoundsGEP(val, idx, "structmembertmp");
			LoadInst* load = Builder.CreateLoad(gep, "structmemberloadtmp");
			return new CGReturnType(load, load->getType(), false, false);
		} else if(isa<CallExprAST>(RHS)){
			// Handle a class method call.
		} else {
			Error("A selection operator must identify an attribute of a structure or a class or call a class method.", this);
		}
	}
	CGReturnType* Rh = RHS->Codegen();
	Value* R = ValueFor(Rh);
	if((Op != "=") && !AreEqualTypes(L->getType(), R->getType())){ 
		if(ShouldCastWhich(L, R) < 0) Error("Cannot perform binary operation on two values of different type.", this);
		printf("Casting binary operands as necessary...\n");
		CastAsNecessary(L, R);
	}
	Value* ret = NULL;
	bool is_f = false;
	int tid = (signed int) L->getType()->getTypeID();
	assert((tid == R->getType()->getTypeID()) || (Op == "="));
	if((tid <= 6) && (tid)) is_f = true;
	else if(tid == 10) is_f = false;
	else {
		if(Op != "="){
			if(!((Op.length() == 2U) && (Op.find("=") != std::string::npos))){
				Error("Invalid operand types for a binary operator.", this);
			} else {
				// For comparisons/compound assignments (<- TODO) this will allow comparisons for pointer types
				if(tid != 14) Error("Invalid operand types for a comparison.", this);
				else {
					is_f = false;
					// Cast each pointer into a 'long' and compare
					assert(CanCastTo(L, Type::getInt64Ty(mod->getContext())));
					tid = 10;
					L = CastTo(L, Type::getInt64Ty(mod->getContext()));
					R = CastTo(R, Type::getInt64Ty(mod->getContext()));
				}
			}
		}
	}
	if(Op == "+") ret = (is_f) ? Builder.CreateFAdd(L, R, "addtmp") : Builder.CreateAdd(L, R, "addtmp");
	else if(Op == "-") ret = (is_f) ? Builder.CreateFSub(L, R, "subtmp") : Builder.CreateSub(L, R, "subtmp");
	else if(Op == "*") ret = (is_f) ? Builder.CreateFMul(L, R, "multmp") : Builder.CreateMul(L, R, "multmp");
	else if(Op == "/") ret = (is_f) ? Builder.CreateFDiv(L, R, "divtmp") : Builder.CreateSDiv(L, R, "divtmp"); // signed division by default
	else if(Op == "<"){
		ret = (is_f) ? Builder.CreateFCmpULT(L, R, "cmptmp") : Builder.CreateICmpSLT(L, R, "cmptmp"); // check for signed less than
		ret = CastTo(ret, L->getType(), false); // cast the result of the comparison to the correct value
	} else if(Op == ">"){
		ret = (is_f) ? Builder.CreateFCmpUGT(L, R, "cmptmp") : Builder.CreateICmpSGT(L, R, "cmptmp"); // check for signed greater than
		ret = CastTo(ret, L->getType(), false); // cast the result of the comparison to the correct value
	} else if(Op == "<="){
		ret = (is_f) ? Builder.CreateFCmpULE(L, R, "cmptmp") : Builder.CreateICmpSLE(L, R, "cmptmp"); // check for signed less than or equal to
		ret = CastTo(ret, L->getType(), false); // cast the result of the comparison to the correct value
	} else if(Op == ">="){
		ret = (is_f) ? Builder.CreateFCmpUGE(L, R, "cmptmp") : Builder.CreateICmpSGE(L, R, "cmptmp"); // check for signed greater than or equal to
		ret = CastTo(ret, L->getType(), false); // cast the result of the comparison to the correct value
	} else if(Op == "=="){
		ret = (is_f) ? Builder.CreateFCmpUEQ(L, R, "cmptmp") : Builder.CreateICmpEQ(L, R, "cmptmp"); // check for equal to
		ret = CastTo(ret, L->getType(), false); // cast the result of the comparison to the correct value
	} else if(Op == "!="){
		ret = (is_f) ? Builder.CreateFCmpUNE(L, R, "cmptmp") : Builder.CreateICmpNE(L, R, "cmptmp"); // check for not equal to
		ret = CastTo(ret, L->getType(), false); // cast the result of the comparison to the correct value
	} else if((Op == "&") || (Op == "&&")){
		// & and && are pretty much one in the same in terms of implementation
		llvm::Type* orig_type = L->getType();
		if(is_f){
			L = CastTo(L, Type::getInt64Ty(mod->getContext()));
			R = CastTo(R, Type::getInt64Ty(mod->getContext()));
		}
		ret = Builder.CreateAnd(L, R, "andtmp");
		ret = CastTo(ret, orig_type); // cast comparison result to original type
	} else if((Op == "|") || (Op == "||")){
		// see note above for & and &&
		llvm::Type* orig_type = L->getType();
		if(is_f){
			L = CastTo(L, Type::getInt64Ty(mod->getContext()));
			R = CastTo(R, Type::getInt64Ty(mod->getContext()));
		}
		ret = Builder.CreateOr(L, R, "ortmp");
		ret = CastTo(ret, orig_type); // cast comparison result to original type
	} else if(Op == "^"){
		llvm::Type* orig_type = L->getType();
		if(is_f){
			L = CastTo(L, Type::getInt64Ty(mod->getContext()));
			R = CastTo(R, Type::getInt64Ty(mod->getContext()));
		}
		ret = Builder.CreateXor(L, R, "xortmp");
		ret = CastTo(ret, orig_type); // cast comparison result to original type
	} else if(Op == "%"){
		ret = (is_f) ? Builder.CreateFRem(L, R, "modtmp") : Builder.CreateSRem(L, R, "modtmp");
		ret = CastTo(ret, L->getType()); // cast comparison result correctly
	} else if(Op == "<<"){
		llvm::Type* orig_type = L->getType();
		if(is_f){
			L = CastTo(L, Type::getInt64Ty(mod->getContext()));
			R = CastTo(R, Type::getInt64Ty(mod->getContext()));
		}
		ret = Builder.CreateShl(L, R, "shltmp");
		ret = CastTo(ret, orig_type); // cast comparison result to original type
	} else if(Op == ">>"){
		llvm::Type* orig_type = L->getType();
		if(is_f){
			L = CastTo(L, Type::getInt64Ty(mod->getContext()));
			R = CastTo(R, Type::getInt64Ty(mod->getContext()));
		}
		ret = Builder.CreateLShr(L, R, "shrtmp"); // logical shift right (arithmetic is available as well as AShr)
		// TODO: Figure out what C uses - arithmetic or logical shift right
		ret = CastTo(ret, orig_type); // cast comparison result to original type
	} else if(Op == "="){
		// This is special --> the assignment operator.
		// TODO/FIXME: Check that a VARIABLE is being assigned, not something else.
		// CHECKME/UPDATE: "Right-associative" assignment operator - implemented in ParseBinOpRHS
		if(!isa<LoadInst>(L)) Error("Left hand side of assignment must be a variable.", this);
		LoadInst* LHS = (LoadInst*) L;
		Value* RHS = R;
		llvm::Type* RHSt = RHS->getType();
		printf("ASGN1\n");
		if(!AreEqualTypes(L->getType(), RHSt)){
			printf("ASGN_TYPE_DUMP:\n");
			L->getType()->dump();
			RHS->getType()->dump();
			printf("\n");
			if(!CanSafelyCastTo(RHS, L->getType())) Error("Cannot assign value of incompatible type to variable.", this);
			RHS = CastTo(RHS, L->getType());
		}
		Builder.CreateStore(RHS, LHS->getPointerOperand(), false); // false=isVolatile
		printf("Generated code for assignment operator.\n");
		ret = RHS; // to allow stuff like (while(x = 2) != EOF), etc.
	}
	// CHECKME: Add bitwise operations (e.g. AND, OR, XOR, etc.)
	// CHECKME: Add boolean operators (e.g. &&, ||)
	if(!ret) ErrorF(this, "Could not perform binary operation or unrecognized binary operator |%s|.", Op.c_str());
	printf("Generated code for a binary expression.\n");
	return new CGReturnType(ret, L->getType(), false, false);
}

CGReturnType* UnaryExprAST::Codegen(void){
	// Note: Unary operators will be assumed to operate on either integral or floating-point values, and nothing else
	// except for the address-of operator (&) and the dereference operator (*).
	// Note 2: Unary operators are NOT guaranteed to return the input type (and in fact, usually don't).
	// TODO/FIXME: All unary operators should have right-associativity, NOT left-associativity.
	printf("Generating code for a unary expression...\n");
	CGReturnType* Onh = on->Codegen();
	Value* On = ValueFor(Onh);
	Value* ret = NULL;
	if((Op != "&") && (Op != "*")){
		bool is_f = false;
		int tid = (signed int) On->getType()->getTypeID();
		if((tid <= 6) && (tid)) is_f = true;
		else if(tid == 10) is_f = false;
		else Error("Invalid types for comparison.", this);
		if(Op == "-"){ // unary negate
			ret = (is_f) ? Builder.CreateFNeg(On, "addtmp") : Builder.CreateNeg(On, "addtmp");
		} else if(Op == "!"){ // logical negation
			ret = CastTo(On, Type::getInt1Ty(mod->getContext())); // get boolean value
			ret = Builder.CreateNot(ret);
		} else if(Op == "~"){ // bitwise NOT
			ret = Builder.CreateNot(On);
		}
	} else {
		if(Op == "&"){
			// We have a given AllocaInst*
			// so make a new one with an additional layer of indirection, store
			// the given in that, and return it
			if(!isa<LoadInst>(On)) Error("Can only take address of variables.", this);
			LoadInst* val = cast<LoadInst>(On);
			On = val->getPointerOperand();
			ret = Builder.CreateAlloca(On->getType(), NULL, "addroftmp");
			Builder.CreateStore(On, ret);
			ret = Builder.CreateLoad(ret, "addroftmpload");
		} else if(Op == "*"){
			// We have a given pointer
			// So return the getPointerOperand()
			if(On->getType()->getTypeID() != llvm::Type::TypeID::PointerTyID) Error("Can only dereference pointers.", this);
			ret = Builder.CreateLoad(On, "dereftmp");
		}
	}
	if(!ret) ErrorF(this, "Could not perform unary operation or unrecognized unary operator |%s|.", Op.c_str());
	printf("Generated code for a unary expression.\n");
	return new CGReturnType(ret, ret->getType(), false, false);
}

CGReturnType* CastExprAST::Codegen(void){
	CGReturnType* typeh = type_to->Codegen();
	llvm::Type* type = (Type*) typeh->val;
	CGReturnType* valh = value->Codegen();
	llvm::Value* val = ValueFor(valh);
	llvm::Value* ret = val;
	if(!AreEqualTypes(type, val->getType())){
		if(!CanCastTo(val, type)) Error("Cannot perform explicit cast.", this);
		ret = CastTo(val, type);
	}
	assert(type->getTypeID() == ret->getType()->getTypeID());
	return new CGReturnType(ret, ret->getType(), false, false);
}

CGReturnType* CallExprAST::Codegen(void){
	/*
	std::vector<Type*> types;
	bool is_extern;
	Function* func;
	Type* RetType;
	
	FuncSymbol(std::vector<Type*> type, bool isExtern, Function* Func, Type* ret_type) :
		types(type), is_extern(isExtern), func(Func), RetType(ret_type) {
			//
		}
	*/
	printf("Generating code for a function call...\n");
	printf("C1\n");
	int arg_num = (signed int) Args.size();
	if(Callee == "return"){
		// Handle the special case of "return"
		if(arg_num && (arg_num != 1)) Error("A 'return' statement takes exactly 1 or no arguments.", this);
		FuncSymbol* sym = cur_func;
		if(!sym) Error("A 'return' statement must be used inside a function.", this);
		llvm::Type* ret_type = sym->RetType;
		if(arg_num){
			CGReturnType* ret_val = Args[0]->Codegen(); // generate the code for the single parameter
			if(!AreEqualTypes(ret_val->type, ret_type)){ 
				if(!CanCastTo(ret_val->type, ret_type)) Error("Conflicting return types.", this);
				ret_val->val = CastTo(ret_val->val, ret_type);
			}
			Builder.CreateRet(ValueFor(ret_val));
		} else {
			// for just 'return' (to return early from a void function for example)
			Builder.CreateRetVoid();
		}
		return new CGReturnType((Value*) 0x01, Type::getVoidTy(mod->getContext()), false, false); // 0x01 is a special code if coming from a "return" codegen
	} else if(Callee == "malloc"){
		// TODO: Reference counting, better errors, detect null pointer derefs, etc.
		// Handle a 'malloc'
		if(arg_num != 1) Error("Malloc takes exactly one argument.", this);
		CGReturnType* sizeh = Args[0]->Codegen(); // size code (e.g. malloc(x))
		Value* size = sizeh->val;
		llvm::Type* size_type = Type::getInt64Ty(mod->getContext());
		if(!AreEqualTypes(size->getType(), size_type)){
			if(!CanCastTo(size->getType(), size_type)) Error("Invalid size for 'malloc'.", this);
			size = CastTo(size, size_type);
		}
		Instruction* ml_inst = CallInst::CreateMalloc(Builder.GetInsertBlock(), size_type, Type::getInt8Ty(mod->getContext()), size);
		Builder.Insert(ml_inst);
		AllocaInst* ptr = Builder.CreateAlloca(PointerType::get(IntegerType::get(mod->getContext(), 8), 0), NULL, "malloc_ptr");
		ptr->setAlignment(8);
		StoreInst* store_inst = Builder.CreateStore(ml_inst, ptr, false); // false = isVolatile
		store_inst->setAlignment(8);
		LoadInst* load = Builder.CreateAlignedLoad(ptr, 8, "malloc_load.ptr");
		return new CGReturnType((Value*) load, load->getType(), false, false);
	} else if(Callee == "free"){
		// Handle a 'free'
		if(arg_num != 1) Error("Free takes exactly one argument.", this);
		CGReturnType* freeh = Args[0]->Codegen();
		Value* free = ValueFor(freeh);
		if(!free->getType()->isPtrOrPtrVectorTy()) Error("Invalid operand for call to 'free'.", this);
		Instruction* fr_inst = CallInst::CreateFree(free, Builder.GetInsertBlock());
		Builder.Insert(fr_inst);
		return new CGReturnType(NULL, Type::getVoidTy(mod->getContext()), false, false);
	}
	VarSymbol* func_ptr_match = NULL; // set to non-null if there is a function pointer match (can only be one due to uniqueness of variable names by scope)
	std::vector<FuncSymbol*> possibs;
	if(FuncTable.find(Callee) == FuncTable.end()){
		func_ptr_match = LookupVar(Callee);
		if(!func_ptr_match || !isa<FunctionType>(func_ptr_match->type->getContainedType(0))) Error("Function '" + Callee + "' not found!", this);
	} else {
		possibs = LookupFunc(Callee); // all the possibilities from function symbol table
	}
	// std::vector<llvm::Type*> type, bool isExtern, Function* Func, llvm::Type* ret_type, FunctionType* func_type)
	if(func_ptr_match){
		// Allow calling a (valid) function pointer //
		func_ptr_match->type->getContainedType(0)->dump();
		assert(isa<FunctionType>(func_ptr_match->type->getContainedType(0)));
		FunctionType* fptr_type = cast<FunctionType>(func_ptr_match->type->getContainedType(0));
		Function* fptr_val = (Function*) Builder.CreateLoad(func_ptr_match->val, "fptrdereftmp"); // load function itself from function pointer
		assert(isa<Function>(fptr_val));
		std::vector<Type*> fptr_params = makeArrayRef(fptr_type->param_begin(), fptr_type->param_end()); // function pointer parameters
		fptr_val->dump();
		possibs.push_back(new FuncSymbol(
			fptr_params, false,
			fptr_val, fptr_type->getReturnType(), fptr_type
		));
	}
	printf("C2\n");
	// FIXME: Add type checking for function calls
	std::vector<FuncSymbol*> matches; // all function matches: "by the book" (exact type matches (e.g. i32 for i32)), or "cast matches"
	std::map<FuncSymbol*, int> cast_matches; // gives FuncSymbol* ==> number of casts required mapping
	std::map<FuncSymbol*, bool> class_matches; // records if it is a class method call from inside the same class or not
	std::vector<CGReturnType*> params;
	std::vector<llvm::Type*> param_types;
	printf("C3\n");
	for(int i = 0; i < arg_num; i++){
		ExprAST* on = Args[i];
		printf("L1\n");
		CGReturnType* ret = on->Codegen();
		printf("L2\n");
		params.push_back(ret);
		param_types.push_back(ret->val->getType());
	}
	// Note: For classes, constructor will not find other methods in class --> WAY too many possible side effects, etc. - will disallow completely by not implementing
	// TODO: Warn about above case
	// If we are emitting for a class and calling a member of the class, add class pointer into the mix
	printf("C4\n");
	// CHECKME: Add ambiguity checks for overloads
	// TODO: Add calling convention check for external functions - maybe add to symbol table 
	// UPDATE: Attributes added to functions to specify, e.g. fastcc - is above check necessary?
	for(std::vector<FuncSymbol*>::iterator it = possibs.begin(); it != possibs.end(); it++){
		FuncSymbol* sym = *it;
		Function* func_on = sym->func;
		std::vector<llvm::Type*> arg_types = sym->types;
		assert(arg_types.size() == func_on->arg_size());
		int taking_num = (signed int) func_on->arg_size(); // number of args this function is taking
		printf("|%d| |%d|\n", (signed int) func_on->arg_size(), arg_num);
		bool num_match = false;
		if(taking_num == arg_num){ // for non-vararg functions
			num_match = true;
		}
		if((func_on->getFunctionType()->isVarArg()) && (taking_num <= arg_num)){ // for vararg functions
			num_match = true;
		}
		class_matches[sym] = false;
		if(EmittingForClass){
			// Check if the called function is a method of the same class
			// If so, and the number of arguments plus one matches the method's arg. num 
			// including the class pointer, pass it through this check.
			// The arg_types class pointer will also be removed so as to allow type checking
			// for the arguments (if check passes).
			printf("Checking for class method call...\n");
			Type* ptr_type = arg_types[0];
			assert(ClassPtrType);
			bool works = true;
			if(!ptr_type->isPointerTy()) works = false;
			else ptr_type = ptr_type->getContainedType(0);
			if(works && isa<StructType>(ptr_type) && (cast<StructType>(ptr_type)->getName() == cast<StructType>(ClassPtrType)->getName())){
				printf("Found class method call from inside same class.\n");
				if(((signed int)(func_on->arg_size() - 1)) == arg_num){ // now check
					class_matches[sym] = true;
					num_match = true;
					arg_types.erase(arg_types.begin());
					--taking_num;
					printf("Passed own class method call.\n");
				}
			}
		}
		if(num_match){
			bool passed = true;
			int casts_needed = 0;
			printf("C4.C1\n");
			for(int i = 0; i < taking_num; i++){
				if(!AreEqualTypes(arg_types[i], param_types[i])){
					printf("here1\n");
					if(!CanSafelyCastTo(params[i]->val, arg_types[i])){ // only allow safe casts now
						passed = false;
						printf("here1-B\n");
						break;
					} else {
						casts_needed++;
					}
					printf("here2\n");
				}
			}
			printf("C4.C2\n");
			if(passed) matches.push_back(sym);
			cast_matches[sym] = casts_needed; // if any arguments needed casting, register this as a "cast match" along with number of casts needed
		}
	}
	printf("C5\n");
	int mc_size = (signed int) matches.size();
	if(!mc_size){ 
		std::cerr << "Could not find a suitable overload for function '" + Callee + "'.\n";
		for(std::vector<FuncSymbol*>::iterator it = possibs.begin(); it != possibs.end(); it++){
			FuncSymbol* sym = *it;
			fprintf(stderr, "Candidate function failed: '%s' with %zu argument(s).\n", Callee.c_str(), sym->func->arg_size());
			NoteFunction(sym);
		}
		Error("No suitable overload found.", this);
	}
	if(mc_size > 1){
		// Attempt to reduce number of matches by seeing which matches needed the fewest, if any, casts.
		std::vector<FuncSymbol*> final_matches;
		int min_casts = (signed int) (Args.size() + 1);
		// Compute lowest number of casts needed
		for(unsigned int i = 0; i < matches.size(); i++){
			//printf("On #%u\n", i);
			if(cast_matches[matches[i]] < min_casts){
				//printf("On %u\n", cast_matches[matches[i]]);
				min_casts = cast_matches[matches[i]];
			}
		}
		// And filter accordingly
		for(unsigned int i = 0; i < matches.size(); i++){
			if(cast_matches[matches[i]] == min_casts){
				//printf("Pushing back #%u...\n", i);
				final_matches.push_back(matches[i]);
			}
		}
		// And set + update
		matches = final_matches;
		mc_size = (signed int) matches.size();
		//printf("MC: %d\n", mc_size);
		//getchar();
	}
	if(mc_size > 1){ // nice error
		// If ambiguity still hasn't been resolved by filtering as above, then error
		fprintf(stderr, "Ambiguous call, %d candidate functions found.\n\n", mc_size);
		std::stringstream ss;
		for(std::vector<FuncSymbol*>::iterator it = matches.begin(); it != matches.end(); it++){
			FuncSymbol* on = *it;
			ss << "Candidate: ";
			if(on->is_extern) ss << "External function ";
			else ss << "User-defined function ";
			if(class_matches[on]) ss << "(in a class) ";
			ss << "'" << Callee << "' ";
			unsigned int p_num = on->types.size();
			ss << "with " << p_num << " parameter";
			if(p_num != 1U) ss << "s"; // U = special suffix for unsigned (like L = long, LL = long long, etc.)
			ss << ".\n";
			std::cerr << ss.str();
			ss.str(""); // clear string stream
			NoteFunction(on);
		}
		Error("Ambiguous call to function.", this);
	}
	printf("C6\n");
	FuncSymbol* matchh = matches[0];
	Function* match = matchh->func;
	if(cast_matches[matchh] > 0){ // if any casting is needed for the parameters to the function, do it now
		std::vector<llvm::Type*> arg_types = matchh->types;
		unsigned int taking_num = match->arg_size();
		if(class_matches[matchh]){
			--taking_num;
			assert(arg_types.size());
			arg_types.erase(arg_types.begin());
		}
		for(unsigned int i = 0; i < taking_num; i++){
			assert(AreEqualTypes(param_types[i], params[i]->val->getType())); // just making sure
			if(!AreEqualTypes(arg_types[i], param_types[i])){
				if(!CanCastTo(params[i]->val, arg_types[i])) Error("Cannot cast parameters for function call.", this);
				params[i]->val = CastTo(params[i]->val, arg_types[i]);
			}
		}
	}
	llvm::Type* ret_type = matchh->RetType;
	std::vector<Value*> ArgsV;
	printf("C7\n");
	if(class_matches[matchh]){
		assert(EmittingForClass && ClassEmittingPtr);
		ArgsV.push_back(ClassEmittingPtr); // add in the implicit class pointer
	}
	for(int i = 0; i < arg_num; i++){
		ArgsV.push_back(params[i]->val);
	}
	printf("C8E\n");
	printf("Generated code for a function call.\n");
	CallInst* call_inst;
	if(!match->getReturnType()->isVoidTy()) call_inst = Builder.CreateCall(match, ArgsV, "calltmp");
	else call_inst = Builder.CreateCall(match, ArgsV, ""); // for void returns, cannot have a named value or verifyModule complains
	call_inst->setTailCall(false);
	call_inst->setCallingConv(CallingConv::C);
	return new CGReturnType(call_inst, ret_type, false, false);
}

CGReturnType* LineExprAST::Codegen(void){
	/*
	std::string LHS; // left hand side (lvalue)
	TypeExprAST* ltype;
	ExprAST* RHS; // right hand side (rvalue)
	std::vector<ExprAST*> LHS_indices; // GEP indices for LHS (only for set's)
	bool is_declaration; // if it is a declaration - if false, it is a mutation
	*/
	printf("Generating code for 'let' or 'set'...\n");
	// TODO: Add "attributes" to customize type of variable (e.g. is constant, linkage type, etc.)
	if(!is_declaration){
		// UPDATING: This will now construct a VariableExprAST in-place and use that for array code generation.
		// Above is made possible by LoadInst's (const) Value* getPointerOperand()
		// UPDATE: 'set' no longer exists in my language. Goodbye.
		assert(false && ("'set' no longer exists!"));
	}
	llvm::Type* type = ltype->Codegen()->type;
	CGReturnType* valh = RHS->Codegen();
	if(VarTable.find(LHS) != VarTable.end()) Error("Cannot redeclare variable '" + LHS + "'.", this); // only searches current scope on purpose
	Value* val = ValueFor(valh);
	std::string offl = "";
	if(val->getName().find(".ptr") != std::string::npos) offl += ".ptr";
	if(!VarTableStack.size()){
		// If we are declaring a global variable, handle it here.
		// Note: Global variables CAN be modified.
		if(!isa<Constant>(val)) Error("Only constant values can initialize global variables.", this);
		GlobalVariable* var = new GlobalVariable(*mod, type, false, llvm::GlobalValue::LinkageTypes::ExternalLinkage, cast<Constant>(val), (LHS + offl)); // external linkage
		VarTable[LHS] = new VarSymbol((Value*) var, type);
		return new CGReturnType((Value*) var, type, true, false); // true = is_alloca
	}
	printf("L1\n");
	if(!AreEqualTypes(type, valh->type)){
		printf("L1B\n"); 
		if(!CanCastTo(val, type)) Error("Cannot assign '" + LHS + "' to incompatible and uncastable type from declared type.", this);
		val = CastTo(val, type);
	}
	printf("L2\n");
	AllocaInst* alloca_inst = Builder.CreateAlloca(type, NULL, LHS + offl);
	Builder.CreateStore(val, alloca_inst, false);
	VarTable[LHS] = new VarSymbol((Value*) alloca_inst, type);
	printf("Generated code for 'let'.\n");
	return new CGReturnType(Builder.CreateLoad(alloca_inst, "loadtmp" + offl), type, false, false);
}

CGReturnType* StructExprAST::Codegen(void){
	/*
	std::string name; // name of struct
	TypeExprAST* struct_type; // struct type
	*/
	printf("Generating code for a struct instantiation...\n");
	if(LookupVar(name) != NULL) Error("Name of '" + name + "' for struct instantiation is already taken.", this);
	Type* type = struct_type->Codegen()->type;
	assert(type);
	if(!isa<StructType>(type)) Error("Struct instantiation must have a struct type.", this);
	AllocaInst* alloca_inst = Builder.CreateAlloca(type, NULL, "struct_" + name);
	VarTable[name] = new VarSymbol((Value*) alloca_inst, type);
	printf("Generated code for a struct instantiation.\n");
	return new CGReturnType(Builder.CreateLoad(alloca_inst, "structloadtmp"), type, false, false);
}

CGReturnType* NewClassExprAST::Codegen(void){
	// NewClassExprAST(const std::string& nm, TypeExprAST* tp, std::vector<ExprAST*>& ct) : name(nm), type(tp), ctor_args(ct)
	printf("Generating code for a class instantiation...\n");
	if(LookupVar(name) != NULL) Error("Name of '" + name + "' for class instantiation is already taken.", this);
	Type* tp = type->Codegen()->type;
	assert(tp);
	if(!isa<StructType>(tp)) Error("Class instantiation must have a class or struct type.", this);
	AllocaInst* alloca_inst = Builder.CreateAlloca(tp, NULL, "class_" + name);
	VarTable[name] = new VarSymbol((Value*) alloca_inst, tp);
	printf("Generated code for a class instantiation.\n");
	return new CGReturnType(Builder.CreateLoad(alloca_inst, "classloadtmp"), tp, false, false);
}

CGReturnType* ArrayExprAST::Codegen(void){
	// TODO: Global arrays with isa<Constant>
	/*
	std::string name; // array name
	TypeExprAST* type; // contained type
	std::vector<ExprAST*> size; // size of array
	std::vector<ExprAST*> initial; // for {...}-style declarations, the initial values of the array
	public:
		ArrayExprAST(std::string Name, TypeExprAST* Type) : name(Name), type(Type) {
			size = 0;
		}
		
		void SetSize(int Size){
			size = Size;
		}
		
		void RegisterInitial(std::vector<ExprAST*>& Initial){
			initial = Initial;
		}
		
		CGReturnType* Codegen(void);
	*/
	Type* type_v = type->Codegen()->type;
	std::vector<int64_t> sizes;
	for(std::vector<ExprAST*>::iterator it = size.begin(); it != size.end(); it++){
		ExprAST* on = *it;
		CGReturnType* genh = on->Codegen();
		if(genh->val->getType()->getTypeID() != 10) Error("Array dimension sizes for declaration must be integers.");
		ConstantInt* cst = (ConstantInt*) genh->val;
		int64_t val = cst->getSExtValue(); // get signed value
		if(val < 0) Error("Array dimension size cannot be negative.");
		sizes.push_back(val);
	}
	if(!sizes.size()) Error("Array must have at least one dimension.");
	std::vector<Type*> types; // ArrayType*'s for each dimension
	for(std::vector<int64_t>::reverse_iterator it = sizes.rbegin(); it != sizes.rend(); it++){
		int64_t on = *it;
		if(!types.size()) types.push_back(ArrayType::get(type_v, on));
		else types.insert(types.begin(), ArrayType::get(types[0], on));
	}
	Value* arr_val = (Value*) new AllocaInst(types[0], "array", Builder.GetInsertBlock()); // does full multi-dimensional alloc
	arr_val->dump();
	//Value* arr_val = Builder.CreateAlloca(type_v, ConstantInt::getSigned(Type::getInt32Ty(mod->getContext()), arr_size), "array");
	if(VarTable.find(name) != VarTable.end()) Error("Cannot redeclare array '" + name + "'.", this);
	if(initial.size()){
		// Set any pre-set values by initializer list
		// TODO: Allow nested {<...>}'s (e.g. { {1, 2}, {3, 4} }
		for(unsigned int i = 0; i < initial.size(); i++){
			CGReturnType* on = initial[i]->Codegen();
			if(!AreEqualTypes(on->type, type_v)){
				if(!CanCastTo(on->type, type_v)) Error("Cannot initialize array with a different and uncastable type.", this);
				on->val = CastTo(on->val, type_v);
			}
			std::vector<Value*> list;
			list.push_back(ConstantInt::get(mod->getContext(), APInt(32, 0))); // step over
			list.push_back(ConstantInt::getSigned((IntegerType*) Type::getInt32Ty(mod->getContext()), (signed int) i));
			Value* gep = Builder.CreateGEP(arr_val, list, "init_list_tmp");
			Builder.CreateStore(on->val, gep, false); // false=isVolatile
		}
	}
	llvm::Type* ret_type = arr_val->getType();
	VarTable[name] = new VarSymbol(arr_val, ret_type);
	return new CGReturnType(arr_val, ret_type, false, false);
}

CGReturnType* StringExprAST::Codegen(void){
	// value == contained value
	printf("Generating code for a string with value |%s|...\n", value.c_str());
	GlobalVariable* gvar = new GlobalVariable(*mod, ArrayType::get(IntegerType::get(mod->getContext(), 8), (value.length() + 1)), true, GlobalValue::PrivateLinkage, NULL, ".str");
	Constant* str = ConstantDataArray::getString(mod->getContext(), StringRef(value.c_str()), true);
	std::vector<Constant*> str_arr;
	Constant* const_0 = ConstantInt::get(mod->getContext(), APInt(32, 0));
	str_arr.push_back(const_0);
	str_arr.push_back(const_0);
	Constant* str_ptr = ConstantExpr::getGetElementPtr(gvar, str_arr);
	gvar->setInitializer(str);
	AllocaInst* ptr = Builder.CreateAlloca(PointerType::get(IntegerType::get(mod->getContext(), 8), 0), NULL, "str_ptr");
	ptr->setAlignment(8);
	StoreInst* store_inst = Builder.CreateStore(str_ptr, ptr, false); // false = isVolatile
	store_inst->setAlignment(8);
	LoadInst* load = Builder.CreateAlignedLoad(ptr, 8, "str_load.ptr");
	printf("Generated string code.\n");
	return new CGReturnType(load, PointerType::get(IntegerType::get(mod->getContext(), 8), 0), false, false);
}

static std::vector<std::tuple<llvm::Type*, std::string> > unfulfilled_allocas; // unfulfilled AllocaInst* queue -> to be created by FunctionAST::Codegen

CGReturnType* PrototypeAST::Codegen(void){
	/*
	std::string Name; // function name
	bool is_extern; // if this is an "external" definition
	std::string ExternType; // if is external, then what type - e.g. "C"
	std::vector<std::string> Args; // name of the arguments passed
	std::vector<TypeExprAST*> Args_Type; // type of arguments passed for each argument
	TypeExprAST* RetType; // return type
	*/
	/*
	std::vector<Type*> types;
	bool is_extern;
	Function* func;
	Type* RetType;
	FunctionType* FuncType;
	
	FuncSymbol(std::vector<Type*> type, bool isExtern, Function* Func, Type* ret_type, FunctionType* func_type) :
		types(type), is_extern(isExtern), func(Func), RetType(ret_type), FuncType(func_type) {
			//
		}
	*/
	assert(Args.size() == Args_Type.size());
	printf("P1\n");
	std::vector<llvm::Type*> types;
	std::vector<llvm::Type*> params;
	for(unsigned int i = 0; i < Args_Type.size(); i++){
		CGReturnType* on = Args_Type[i]->Codegen();
		types.push_back(on->type);
		params.push_back(types[i]);
	}
	printf("P2\n");
	CGReturnType* ret_typeh = RetType->Codegen();
	llvm::Type* ret_type = ret_typeh->type;
	//printf("ID: |%d|.\n", (int) ret_type->getTypeID());
	FunctionType* FT = FunctionType::get(ret_type, params, isVarArg); // supports variable argument functions now
	// TODO: Handle external properly for different languages (e.g. C, Haskell, etc.)
	printf("P3\n");
	Function* F = Function::Create(FT, Function::ExternalLinkage, Name, mod);
	int i = 0;
	printf("P4\n");
	for(Function::arg_iterator it = F->arg_begin(); i < (signed int) Args.size(); i++, it++){
		it->setName(Args[i]);
		printf("Pushing #%d into alloca queue...\n", i);
		bool adding = !is_extern; // if pushing into alloca queue
		if(adding){ 
			unfulfilled_allocas.push_back(std::make_tuple(types[i], Args[i])); // push this request into alloca queue to add to entry point if required
		}
	}
	//printf("Alloca queue size: %d.\n", (signed int) unfulfilled_allocas.size());
	printf("P5\n");
	F->setCallingConv(CallingConv::C); // set the calling convention to C's by default
	if(std::find(Attrs.begin(), Attrs.end(), "fastcc") != Attrs.end()){
		// Use a "fast" calling convention
		F->setCallingConv(CallingConv::Fast);
	}
	// Set attributes --> nounwind and uwtable
	AttributeSet FAttribs;
	SmallVector<AttributeSet, 4> Attrs_vec;
	AttributeSet FAttribList;
	AttrBuilder ABuilder;
	ABuilder.addAttribute(Attribute::NoUnwind);
	ABuilder.addAttribute(Attribute::UWTable);
	if(std::find(Attrs.begin(), Attrs.end(), "inline") != Attrs.end()){
		ABuilder.addAttribute(Attribute::InlineHint);
	} else {
		// If inlining is not explicitly asked for, will not be done.
		ABuilder.addAttribute(Attribute::NoInline);
	}
	if(std::find(Attrs.begin(), Attrs.end(), "optsize") != Attrs.end()){
		// Optimize function for size
		ABuilder.addAttribute(Attribute::OptimizeForSize);
		if(std::find(Attrs.begin(), Attrs.end(), "optnone") != Attrs.end()) Error("Cannot optimize function for size and not at all at the same time!", this);
	} else if(std::find(Attrs.begin(), Attrs.end(), "optnone") != Attrs.end()){
		// Don't optimize function at all
		ABuilder.addAttribute(Attribute::InlineHint);
	}
	if(std::find(Attrs.begin(), Attrs.end(), "noreturn") != Attrs.end()){
		ABuilder.addAttribute(Attribute::NoReturn);
	}
	FAttribList = AttributeSet::get(mod->getContext(), ~0U, ABuilder);
	Attrs_vec.push_back(FAttribList);
	FAttribs = AttributeSet::get(mod->getContext(), Attrs_vec);
	F->setAttributes(FAttribs);
	// Insert into function symbol table
	if(FuncTable.find(Name) == FuncTable.end()){
		// First function with this name is being defined
		std::vector<FuncSymbol*> vec; // create the vector
		cur_func = new FuncSymbol(types, is_extern, F, RetType->Codegen()->type, FT);
		vec.push_back(cur_func);
		FuncTable[Name] = vec;
		function_map[cur_func] = this;
		function_sym_map[F] = cur_func;
	} else {
		// Adding an overload otherwise
		cur_func = new FuncSymbol(types, is_extern, F, RetType->Codegen()->type, FT);
		FuncTable[Name].push_back(cur_func);
		function_map[cur_func] = this;
		function_sym_map[F] = cur_func;
	}
	printf("P6E\n");
	return new CGReturnType((Value*) F, RetType->Codegen()->type, false, true);
}

CGReturnType* FunctionAST::Codegen(void){
	CGReturnType* Protoh = Proto->Codegen(); // generate code for the prototype
	printf("F1\n");
	if(!Protoh->is_func) Error("Invalid prototype code generated.", this);
	Function* Func = (Function*) Protoh->val;
	PushVarScope(); // make function var sub-scope
	printf("F2\n");
	BasicBlock* BB = BasicBlock::Create(mod->getContext(), "entry", Func);
	Builder.SetInsertPoint(BB);
	printf("F3 - Unfulfilled Allocas\n");
	ClassEmittingPtr = (Value*) NULL;
	if(EmittingClassCtor){
		// If emitting the constructor, create the return class struct
		assert(ClassPtrType);
		ClassEmittingPtr = Builder.CreateAlloca(ClassPtrType, NULL, "__class_ptr_ctor");
	}
	if(EmittingForClass || EmittingClassCtor){
		// Note: This creates and pops a new sub-scope in addition to the function sub-scope
		// to use the function sub-scope as a scope for the class ivars.
		// RegisterIVar
		for(Function::arg_iterator it = Func->arg_begin(); it != Func->arg_end(); it++){
			// Quickly get the ClassEmittingPtr right now if needed
			if(it->getName().find("__class_ptr") != std::string::npos){
				ClassEmittingPtr = (Value*) it; // the argument itself is the implicit class pointer
				break;
			}
		}
		ClassEmittingPtr->dump();
		assert(ClassPtrType && ClassEmittingPtr && isa<StructType>(ClassPtrType));
		assert(StructMemberTable.find((StructType*) ClassPtrType) != StructMemberTable.end());
		std::string name = GetProto()->Name;
		auto on = StructMemberTable[(StructType*) ClassPtrType];
		for(auto& t_on : on){
			// Make sure no naming conflicts exist as well
			// std::tuple<std::string, Type*>
			if(std::get<0>(t_on) == name){
				Error("Cannot declare a class method with the same name as a class instance variable.", this);
			}
		}
		std::vector<std::tuple<std::string, Type*> > s_tbl = StructMemberTable[(StructType*) ClassPtrType];
		for(std::tuple<std::string, Type*> on : s_tbl){
			std::tuple<int, Type*> off = GetStructOffsetFor((StructType*) ClassPtrType, std::get<0>(on));
			std::vector<Value*> idx;
			idx.push_back(ConstantInt::get(mod->getContext(), APInt(32, 0)));
			idx.push_back(ConstantInt::get(mod->getContext(), APInt(32, std::get<0>(off))));
			Value* gep = Builder.CreateInBoundsGEP(ClassEmittingPtr, idx, "__classmembergeptmp");
			VarSymbol* var_sym = new VarSymbol(gep, gep->getType());
			var_sym->RegisterIVar();
			VarTable[std::get<0>(on)] = var_sym;
		}
		PushVarScope(); // make another sub-scope to actually use as the function's (current one was used for ivars)	
	}
	int i = 0;
	for(Function::arg_iterator it = Func->arg_begin(); i < (signed int) unfulfilled_allocas.size(); i++, it++){
		printf("Fulfilling #%d of %d...\n", i, (signed int) unfulfilled_allocas.size());
		std::tuple<llvm::Type*, std::string>& on = unfulfilled_allocas[i];
		bool adding = true; // if inserting this into the variable symbol table
		if(EmittingForClass && (std::get<1>(on).find("__class_ptr") != std::string::npos)){
			adding = false;
		}
		if(adding){
			AllocaInst* alloca_inst = Builder.CreateAlloca(std::get<0>(on), NULL, std::get<1>(on) + ".ptr");
			Builder.CreateStore(it, alloca_inst, false); // false=isVolatile
			if(VarTable.find(std::get<1>(on)) != VarTable.end()) Error("Cannot redeclare function variable '" + std::get<1>(on) + "'.", this);
			VarTable[std::get<1>(on)] = new VarSymbol((Value*) alloca_inst, std::get<0>(on)); // add parameters to variable symbol table if required
		}
	}
	unfulfilled_allocas.clear(); // clear vector
	printf("F4 - Body gen\n");
	for(std::vector<ExprAST*>::iterator it = Body.begin(); it != Body.end(); it++){
		(*it)->Codegen();
	}
	if(Func->getReturnType()->isVoidTy()) Builder.CreateRetVoid(); // if the function has a void return type, create a "ret void" instruction
	if(EmittingClassCtor){
		// Handle the constructor return by making it return the class struct
		Builder.CreateRet(ClassEmittingPtr);
	}
	if(EmittingForClass || EmittingClassCtor){
		PopVarScope(); // pop the additional var-scope created due to ivars' scoping necessity
	}
	printf("F5E\n");
	PopVarScope(); // pop sub-scope
	// Now ensure that functions with a non-void return type DO return and some other class-related things //
	if(!Func->getReturnType()->isVoidTy()){
		for(BasicBlock& bl : *Func){
			if(!bl.getTerminator()){
				printf("Block dump:\n");
				bl.dump();
				printf("\n");
				NoteFunction(Func);
				Error("Function of non-void return type must return a value.", this);
			}
			/*
			if(EmittingClassCtor && (bl != Func->back())){
				if(isa<ReturnInst>(bl.getTerminator())){
					NoteFunction(Func);
					Error("Class constructor cannot return.", this);
				}
			}
			*/
		}
	}
	std::string err;
	raw_string_ostream strfp(err);
	if(verifyFunction(*Func, &strfp)){ // verify function, check for inconsistencies
		Func->dump();
		std::cerr << "\n" << strfp.str() << " - " << err << "\n";
		Error("Could not verify function.", this);
	}
	/*
	void *FPtr = TheExecutionEngine->getPointerToFunction(LF);
      
      // Cast it to the right type (takes no arguments, returns a double) so we
      // can call it as a native function.
      double (*FP)() = (double (*)())(intptr_t)FPtr;
      fprintf(stderr, "Evaluated to %f\n", FP());
    */
    if(ShouldOptimize) TheFPM->run(*Func); // optimize function
	return new CGReturnType((Value*) Func, Protoh->type, false, true);
}

CGReturnType* ClassExprAST::Codegen(void){
	// ClassExprAST(const std::string& nm, const std::vector<std::tuple<TypeExprAST*, std::string> >& ivr, const std::vector<FunctionAST*>& mbs) 
	// Name, ivars, members
	// A class is just a structure with members that all take an implicit pointer to the aforementioned structure, so it is implemented as such //
	// First, create the structure and its associated type (as well as register its members) //
	StructType* class_struct = StructType::create(mod->getContext(), ("class_struct." + Name));
	if(TypeTable.find(Name) != TypeTable.end()) Error("Cannot redeclare struct/class '" + Name + "'.", this);
	TypeTable[Name] = (Type*) class_struct;
	assert(class_struct->hasName());
	std::vector<Type*> tp;
	std::vector<std::tuple<std::string, Type*> > tbl;
	for(std::tuple<TypeExprAST*, std::string> on : ivars){
		TypeExprAST* on_h = std::get<0>(on);
		CGReturnType* onh = on_h->Codegen();
		assert(onh->val);
		Type* on_type = (Type*) onh->val;
		if(!StructType::isValidElementType(on_type)) Error("Element '" + std::get<1>(on) + "' is not a valid instance variable type.", this);
		tp.push_back(on_type);
		tbl.push_back(std::make_tuple(std::get<1>(on), on_type));
	}
	class_struct->setBody(tp);
	assert(!class_struct->isOpaque() && !class_struct->isPacked());
	printf("Struct type dump:\n");
	class_struct->dump();
	printf("\n");
	assert(StructMemberTable.find(class_struct) == StructMemberTable.end());
	StructMemberTable[class_struct] = tbl; // register members by struct type so existing code for using struct members can be leveraged
	// Now, set up the nested namespace and emit all class methods along with their implicit structure pointers into it //
	PushFuncScope();
	PushVarScope(); // also one for safety/later use
	/*
	std::string Name; // function name
	bool is_extern; // if this is an "external" definition
	std::string ExternType; // if is external, then what type - e.g. "C"
	std::vector<std::string> Args; // name of the arguments passed
	std::vector<TypeExprAST*> Args_Type; // type of arguments passed for each argument
	std::vector<std::string> Attrs; // any additional attributes specified
	TypeExprAST* RetType; // return type
	bool isVarArg; // if this is a vararg function (has a tok_elipsis at end) or not
	*/
	/*
	static bool EmittingForClass = false; // whether emitting code for a class member currently or not (will not be set if emitting for ctor/dtor)
	static Type* ClassPtrType = NULL; // type of class ptr for current class
	static Value* ClassEmittingPtr = NULL; // when emitting for a class, the implicit class pointer is set for abstracting away ivar details
	static bool EmittingClassCtor = false; // whether emitting for a class ctor
	*/
	TypeExprAST* class_struct_tp = new TypeExprAST(Name); 
	class_struct_tp->SetDepth(1); // since the implicit class *pointer* is a *pointer*
	const std::string class_ptr_name = "__class_ptr";
	std::vector<std::tuple<std::string, FuncSymbol*> > class_funcs;
	for(FunctionAST* on : members){
		// TODO/FIXME: Let class methods see the class's instance variables and finish up them calling each other, etc.
		// TODO/FIXME: Make CallExprAST/other ignore the first argument (pointer to struct) when dealing with overloading, etc.
		// TODO/FIXME: Finish ctor, dtor, etc.
		PrototypeAST* proto = on->GetProto();
		ClassPtrType = (Type*) class_struct;
		if(proto->Name == Name){
			// We are emitting code for the constructor.
			EmittingForClass = false; // don't want the implicit pointer added for the ctor --> it MAKES the pointer...
			EmittingClassCtor = true;
			proto->RetType = class_struct_tp; // the constructor always returns the class struct type (a pointer to it, rather)
		} else {
			// Add pointer to param list, etc.
			proto->Args_Type.insert(proto->Args_Type.begin(), class_struct_tp);
			proto->Args.insert(proto->Args.begin(), class_ptr_name);
			EmittingForClass = true;
			EmittingClassCtor = false;
		}
		Function* func = (Function*) on->Codegen()->val;
		assert(func);
		class_funcs.push_back(std::make_tuple(proto->Name, function_sym_map.at(func)));
		EmittingForClass = false; // reset this after each function emitted
	}
	PopVarScope();
	PopFuncScope();
	// static std::map<StructType*, std::vector<std::tuple<std::string, FuncSymbol*> > > ClassMemberTable
	ClassMemberTable[class_struct] = class_funcs;
	return new CGReturnType((Value*) class_struct, (Type*) class_struct, false, false);
}

CGReturnType* IfExprAST::Codegen(void){
	/*
	ExprAST* cond; // the condition to be evaluated
	std::vector<ExprAST*> if_true; // the "if true" or "then" branch
	std::vector<ExprAST*> if_false; // the "if false" or "else" branch
	public:
		IfExprAST(ExprAST* Cond, ExprAST* IfTrue, ExprAST* IfFalse) : cond(Cond) {
			if_true.push_back(IfTrue);
			if_false.push_back(IfFalse);
		}
		
		IfExprAST(ExprAST* Cond, std::vector<ExprAST*> IfTrue, std::vector<ExprAST*> IfFalse) : cond(Cond), if_true(IfTrue), if_false(IfFalse) {
			// not much... at all
		}
	*/
	CGReturnType* condh = cond->Codegen();
	Value* cond_v = condh->val;
	cond_v = CastTo(cond_v, Type::getDoubleTy(mod->getContext())); // for final boolean evaluation, convert to an f64 (double), and compare it against 0
	Value* ctrl_0 = ConstantFP::get(mod->getContext(), APFloat(0.0)); // the "control" value, or 0, casted to an f64 (double)
	ctrl_0 = CastTo(ctrl_0, Type::getDoubleTy(mod->getContext())); // casting control value
	Value* cond_val = Builder.CreateFCmpONE(cond_v, ctrl_0, "if.cond"); // convert condh->val to i1 bool
	Function* cur_func = Builder.GetInsertBlock()->getParent(); // let the builder keep track of this stuff...
	// Create the blocks for each branch
	BasicBlock* TrueBr = BasicBlock::Create(mod->getContext(), "if.true", cur_func); // true branch
	BasicBlock* FalseBr = BasicBlock::Create(mod->getContext(), "if.false"); // false branch - currently unlinked
	BasicBlock* MergeBr = BasicBlock::Create(mod->getContext(), "if.merge"); // merge branch - currently unlinked
	bool true_term = false, false_term = false; // to deal with "return" statements inside the body of the if/else
	// Create the main conditional jump
	Builder.CreateCondBr(cond_val, TrueBr, FalseBr);
	// Emit "true" branch code
	PushVarScope(); // Create a new sub-scope for the if true branch
	Builder.SetInsertPoint(TrueBr);
	for(unsigned int i = 0; i < if_true.size(); i++){
		CGReturnType* got = if_true[i]->Codegen();
		if(got->val == (Value*) 0x01){ // special "return" codegen val
			true_term = true;
			break;
		}
	}
	PopVarScope(); // Destroy if true branch sub-scope
	if(!true_term) Builder.CreateBr(MergeBr); // terminator for true branch
	// Emit "false" branch code
	cur_func->getBasicBlockList().push_back(FalseBr); // link "FalseBR" to current function at end
	PushVarScope(); // Create a new sub-scope for the if false branch
	Builder.SetInsertPoint(FalseBr);
	for(unsigned int i = 0; i < if_false.size(); i++){
		if(if_false[i]){ // ensure it is not NULL
			CGReturnType* got = if_false[i]->Codegen();
			if(got->val == (Value*) 0x01){ // special "return" codegen val
				false_term = true;
				break;
			}
		}
	}
	PopVarScope(); // Destroy if false branch sub-scope
	if(!false_term) Builder.CreateBr(MergeBr); // terminator for false branch
	// Emit "merge" point - but only if either the true or the false branch has not already been terminated
	if(!(true_term && false_term)) cur_func->getBasicBlockList().push_back(MergeBr); // link "MergeBr" to current function at end
	Builder.SetInsertPoint(MergeBr);
	if(!(true_term && false_term)) return new CGReturnType(NULL, Type::getVoidTy(mod->getContext()), false, false);
	else return new CGReturnType((Value*) 0x01, Type::getVoidTy(mod->getContext()), false, false); // handle else if returns
}

CGReturnType* WhileExprAST::Codegen(void){
	/*
	ExprAST* cond; // the condition to be evaluated at the start of every loop
	std::vector<ExprAST*> body; // the body of the while loop
	public:
		WhileExprAST(ExprAST* Cond, ExprAST* Body) : cond(Cond) {
			body.push_back(Body);
		}
		
		WhileExprAST(ExprAST* Cond, std::vector<ExprAST*> Body) : cond(Cond), Body(body) {
			// nothing - really!
		}
	*/
	Function* cur_func = Builder.GetInsertBlock()->getParent();
	// Set up blocks for loop
	BasicBlock* loop_test = BasicBlock::Create(mod->getContext(), "while.cond", cur_func);
	BasicBlock* loop_block = BasicBlock::Create(mod->getContext(), "while.body"); // while loop body
	BasicBlock* loop_merge = BasicBlock::Create(mod->getContext(), "while.merge"); // after the while loop
	// Set Up loop conditional check block
	Builder.CreateBr(loop_test); // jump to while condition check and terminate current block
	PushVarScope(); // create a new sub-scope for the while loop body
	Builder.SetInsertPoint(loop_test);
	// Evaluate conditional in loop conditional block
	CGReturnType* condh = cond->Codegen();
	Value* cond_v = condh->val;
	cond_v = CastTo(cond_v, Type::getDoubleTy(mod->getContext())); // for final boolean evaluation, convert to an f64 (double), and compare it against 0
	Value* ctrl_0 = ConstantFP::get(mod->getContext(), APFloat(0.0)); // the "control" value, or 0, casted to an f64 (double)
	ctrl_0 = CastTo(ctrl_0, Type::getDoubleTy(mod->getContext())); // casting control value
	Value* cond_val = Builder.CreateFCmpONE(cond_v, ctrl_0, "cond.conv"); // convert condh->val to i1 bool
	// Create the main conditional jump
	Builder.CreateCondBr(cond_val, loop_block, loop_merge);
	// Generate body of while loop
	cur_func->getBasicBlockList().push_back(loop_block);
	Builder.SetInsertPoint(loop_block); // start inserting into while loop body
	bool termed = false;
	for(unsigned int i = 0; i < body.size(); i++){
		if(body[i]->Codegen()->val == (Value*) 0x01){ // if there is a return (an early terminator)
			termed = true;
			break;
		}
	}
	if(!termed) Builder.CreateBr(loop_test); // since this is a loop, jump back to conditional evaluation - assuming no return's are in the body, of course
	// Generate merge block
	cur_func->getBasicBlockList().push_back(loop_merge);
	Builder.SetInsertPoint(loop_merge);
	PopVarScope(); // Destroy sub-scope for loop
	return new CGReturnType((termed) ? ((Value*) 0x01) : NULL, Type::getVoidTy(mod->getContext()), false, false); // do special return type if necessary
}

CGReturnType* ForExprAST::Codegen(void){
	/*
	ExprAST* init; // the "initialization" part of the loop
	ExprAST* cond; // the condition to be evaluated every time the loop runs
	ExprAST* incr; // the "increment" statement or such
	std::vector<ExprAST*> body; // the body of the for loop
	public:
		ForExprAST(ExprAST* Init, ExprAST* Cond, ExprAST* Incr) : init(Init), cond(Cond), incr(Incr) {
			// nothing = win
		}
		
		void RegisterBody(ExprAST* Body){
			body.push_back(Body);
		}
		
		void RegisterBody(std::vector<ExprAST*> Body){
			body = Body;
		}
	*/
	Function* cur_func = Builder.GetInsertBlock()->getParent();
	// Set up blocks for loop
	BasicBlock* loop_test = BasicBlock::Create(mod->getContext(), "for.cond", cur_func); // this checks the condition
	BasicBlock* loop_block = BasicBlock::Create(mod->getContext(), "for.body"); // for loop body - increment is at end
	BasicBlock* loop_merge = BasicBlock::Create(mod->getContext(), "for.merge"); // after the for loop
	PushVarScope(); // create loop sub-scope
	// Do initialization
	if(init) init->Codegen(); // if an initialization exists, do it before we start emitting the loop condition block
	Builder.CreateBr(loop_test);
	// Do condition checking and branch as necessary
	Builder.SetInsertPoint(loop_test);
	Value* cond_val; // final condition value (i1 0 or i1 1)
	if(cond){
		CGReturnType* condh = cond->Codegen();
		Value* cond_v = condh->val;
		cond_v = CastTo(cond_v, Type::getDoubleTy(mod->getContext())); // cast to double
		Value* ctrl_0 = ConstantFP::get(mod->getContext(), APFloat(0.0)); // f64 0.0
		ctrl_0 = CastTo(ctrl_0, Type::getDoubleTy(mod->getContext())); // cast control value
		cond_val = Builder.CreateFCmpONE(cond_v, ctrl_0, "cond.conv"); // convert to bool by comparing against f64 0.0 for inequality
	} else cond_val = Builder.CreateFCmpONE(ConstantFP::get(mod->getContext(), APFloat(1.0)), ConstantFP::get(mod->getContext(), APFloat(0.0)), "cond.conv"); // always true if no condition exists
	// Conditional jump
	Builder.CreateCondBr(cond_val, loop_block, loop_merge);
	// Generate loop body
	cur_func->getBasicBlockList().push_back(loop_block);
	Builder.SetInsertPoint(loop_block);
	bool termed = false;
	for(unsigned int i = 0; i < body.size(); i++){
		if(body[i]->Codegen()->val == (Value*) 0x01){ // if there is a return (an early terminator)
			termed = true;
			break;
		}
	}
	if(!termed){ // make sure no duplicate terminators are added (return, br, etc. = terminators)
		if(incr) incr->Codegen(); // do the increment if it exists
		Builder.CreateBr(loop_test); // re-check the condition
	}
	PopVarScope(); // destroy loop sub-scope
	// Generate merge block to allow for more codegen'ing later
	cur_func->getBasicBlockList().push_back(loop_merge);
	Builder.SetInsertPoint(loop_merge);
	return new CGReturnType((termed) ? ((Value*) 0x01) : NULL, Type::getVoidTy(mod->getContext()), false, false); // do special return type if necessary
}

// Note: No topLevelExpr's in this language since this is NOT a functional language nor is it meant to be.

static void HandleTypeDef(void){
	std::cerr << "Parsing a type definition...\n";
	ParseTypeDef();
}

static void HandleGlobalLet(void){
	std::cerr << "Parsing a global variable...\n";
	if(ExprAST* let_ast = ParseLine()){
		std::cerr << "Parsed a global variable.\n";
		let_ast->Codegen();
	}
}

static void HandleDefinition(void){
	std::cerr << "Parsing a function definition and body...\n";
	if(FunctionAST* func_ast = (FunctionAST*) ParseDefinition()){
		std::cerr << "Parsed a function definition and body.\n";
		CGReturnType* funch = func_ast->Codegen();
		Function* func = (Function*) funch->val; // for JIT use later, maybe? or optimizations
		if(func)
			;
	}
}

static void HandleExtern(void){
	std::cerr << "Parsing an external declaration...\n";
	if(PrototypeAST* extern_ast = (PrototypeAST*) ParseExtern()){
		std::cerr << "Parsed an external declaration.\n";
		extern_ast->Codegen();
	}
}

static void HandleStructDef(void){
	std::cerr << "Parsing a 'struct' definition...\n";
	ExprAST* ret = ParseStructTypeRef();
	std::cerr << "Parsed a 'struct' definition.\n";
	ret->Codegen();
}

static void HandleClassDef(void){
	std::cerr << "Parsing a class definition...\n";
	ExprAST* ret = ParseClassExpr();
	std::cerr << "Parsed a class definition.\n";
	ret->Codegen();
}

// top ::= definition | external | expression
static void MainLoop(void){
	std::cerr << "Parsing...\n";
	while(true){
		switch(CurTok){
			case tok_eof: return;
			case tok_def: return; // haven't implemented operator overloading yet
			case tok_typedef: HandleTypeDef(); break;
			case tok_import: // haven't implemented C-preprocessor-style includes or any other import styles - consider linking it externally?
				getNextToken();
				assert(CurTok == tok_id);
				getNextToken();
				assert(CurTok == ';');
				getNextToken();
				break;
			case tok_func: HandleDefinition(); break;
			case tok_extern: HandleExtern(); getNextToken(); break;
			case tok_struct: HandleStructDef(); break;
			case tok_let: HandleGlobalLet(); break;
			case tok_class: HandleClassDef(); break;
			default: ErrorF(NULL, "Unexpected token |%c| or |%d| after parsing.", (char) CurTok, CurTok); return;
		}
	}
}

void FillInLines(std::string& contents, std::vector<std::tuple<std::string, unsigned int> >& starts){
	/*
	unsigned int c = 0;
	std::tuple<std::string, unsigned int> on = starts[c];
	std::tuple<std::string, unsigned int> next;
	if(starts.find(c + 1) != starts.end()){ 
		next = starts[c + 1];
	}
	for(unsigned int i = 0; i < contents.length(); i++){
		if(starts.find(c + 1) != starts.end()){
			unsigned int st = std::get<1>(next);
			if(i == st){
				// onto a different file now
				on = next;
				next = starts[c + 1];
				++c;
			}
		}
		if(contents[i] == '\n'){ 
			line_starts.push_back(std::make_tuple((signed int) i, std::get<0>(on)));
		}
	}
	*/
	if(!contents.size()) return;
	printf("Filling in lines...\n");
	for(auto& on : starts) printf("Have tuple: <%s, %u>\n", std::get<0>(on).c_str(), std::get<1>(on));
	std::string file_on = "";
	for(unsigned int i = 0; i < contents.length(); i++){
		unsigned int ct = 0;
		for(auto& on : starts){
			if(std::get<1>(on) == i){
				if(!file_on.length()){
					// Add initial line
					line_starts.push_back(std::make_tuple(0, std::get<0>(on)));
				}
				file_on = std::get<0>(on);
				printf("Now on file |%s| at |%u|\n", file_on.c_str(), i);
			}
			++ct;
		}
		if(contents[i] == '\n'){
			line_starts.push_back(std::make_tuple((signed int) i, file_on));
		}
	}
	printf("Filled in lines!\n");
}

std::string ReadFile(std::string fname){
	std::ifstream in(fname, std::ios::in);
	if(in){
		std::string contents;
		in.seekg(0, std::ios::end);
		contents.resize(in.tellg());
		in.seekg(0, std::ios::beg);
		in.read(&contents[0], contents.size());
		in.close();
		return contents;
	}
	throw(errno); // throw the system-level errno otherwise
}

void ResetLexer(void){
	// This resets all of the lexer's data EXCEPT for the actual FileData.
	/*
	static std::string IdStr; // current identifier - will be filled in if it is a tok_id
	static double NumVal; // current number value - will be filled in if it is a tok_num - can be casted to int, etc. as requested or specified
	static std::string LastOp = ""; // current operator recognized - will be filled in if it is a tok_op

	static std::string FileData; // contents of file provided
	static int LastIndex = 0; // index on for the FileData
	static int LastChar = ' '; // let the gettok function remember the last character read
	static int FileDataLength; // length of FileData - calculated once
	static bool InString = false; // check if currently in a string
	static bool had_dec_point = false; // if the number scanned in had a decimal point

	static std::vector<int> line_starts; // the starts of lines in the original file
	static std::map<std::string, int> BinOpPrec; // binary operator precedence --> and as such, functions as the list of registered binary operators
	static std::map<char, bool> UnaryOps; // registered unary operators (limited to length 1, no precedence needed)
	*/
	IdStr = "";
	NumVal = 0.0;
	LastOp = "";
	LastIndex = 0;
	LastChar = ' ';
	FileDataLength = 0;
	InString = false;
	had_dec_point = false;
	line_starts.clear();
}

void Preprocess(std::string orig_file){
	printf("Preprocessing file...\n");
	const std::string lib_prefix = "lib", lib_suffix = ".txt";
	getNextToken();
	std::vector<std::string> imports;
	while(CurTok != tok_eof){
		while((CurTok != tok_import) && (CurTok != tok_eof)){
			getNextToken();
		}
		// import
		//	::= 'import' id ';'
		if(CurTok == tok_import){
			getNextToken();
			if(CurTok != tok_id) Error("Expected library name after 'import'.");
			imports.push_back(IdStr);
			getNextToken();
			if(CurTok != ';') Error("Expected a ';' after importing library.");
			getNextToken();
		}
	}
	ResetLexer();
	std::string import_data = "";
	std::vector<std::tuple<std::string, unsigned int> > starts;
	for(std::string on : imports){
		std::string have = "";
		try {
			have = ReadFile(lib_prefix + on + lib_suffix);
		} catch(...){
			Error("Could not read library '" + on + "'!");
		}
		starts.push_back(std::make_tuple((lib_prefix + on + lib_suffix), import_data.length()));
		import_data += have;
	}
	std::string final_data = import_data + FileData;
	starts.push_back(std::make_tuple(orig_file.c_str(), import_data.length()));
	FillInLines(final_data, starts); // FIXME/FINISHME: use ACTUAL line numbers, NOT preprocessed line numbers with file includes - use offset to start from?
	FileDataLength = (signed int) final_data.length();
	FileData = final_data;
	printf("Preprocessed file!\n");
}

int op_lvl = 2; // -O2 by default

std::string linker_options = "-lm ";

int Compile(std::string file_name, std::string out_name){
	// Compiles the selected file into the selected output file and returns status (0 = fine, anything else is failure to compile) //
	// Set up LLVM module and context.
	LLVMContext& Context = getGlobalContext();
	mod = new Module("", Context);
	std::string err;
	/*
	// Set up JIT and optimizations
	TheExecutionEngine = EngineBuilder(mod).setErrorStr(&err).create();
	if(!TheExecutionEngine) ErrorF("Could not create JIT: %s\n", err.c_str());
	*/
	FunctionPassManager OurFPM(mod);
	// Set up the optimizer pipeline.  Start with registering info about how the
	// target lays out data structures.
	mod->setDataLayout("e-p:64:64:64-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:64:64-f32:32:32-f64:64:64-v64:64:64-v128:128:128-a0:0:64-s0:64:64-f80:128:128-n8:16:32:64-S128");
	mod->setTargetTriple("x86_64-apple-macosx10.8.0");
	// Add optimization passes. //
	// Do simple "peephole" optimizations and bit-twiddling options.
	OurFPM.add(createInstructionCombiningPass()); // Note: This optimization is required for target lowering to succeed
	if(op_lvl > 1){
		OurFPM.add(createBasicAliasAnalysisPass()); // Provide basic AliasAnalysis support for GVN.
		OurFPM.add(createReassociatePass()); // Reassociate expressions.
		if(op_lvl > 2){
			OurFPM.add(createGVNPass()); // Eliminate Common SubExpressions.
			OurFPM.add(createCFGSimplificationPass()); // Simplify the control flow graph (deleting unreachable blocks, etc).
			OurFPM.add(createPromoteMemoryToRegisterPass());
		}
	}
	OurFPM.doInitialization();
	// Set the global so the code gen can use this.
	TheFPM = &OurFPM;
	// Set up binary operator precedence.
	BinOpPrec["="] = 2; // lowest precedence for the assignment operator
	BinOpPrec["||"] = 5;
	BinOpPrec["&&"] = 6;
	BinOpPrec["|"] = 7;
	BinOpPrec["^"] = 8;
	BinOpPrec["&"] = 9;
	BinOpPrec["=="] = BinOpPrec["!="] = 10; // (*)[-]equality operators
	BinOpPrec["<"] = BinOpPrec[">"] = 11; // (*) than operators
	BinOpPrec["<="] = BinOpPrec[">="] = 11; // (*) OR equal to operators
	BinOpPrec["<<"] = BinOpPrec[">>"] = 12; // bitwise shift operators
	BinOpPrec["+"] = BinOpPrec["-"] = 15;
	BinOpPrec["%"] = BinOpPrec["*"] = BinOpPrec["/"] = 20;
	BinOpPrec["--"] = BinOpPrec["++"] = 30; // TODO/FIXME: Handle unary-style increment/decrement (prefix)
	BinOpPrec["."] = BinOpPrec["->"] = 40;
	// Set up unary operators.
	UnaryOps['~'] = true;
	UnaryOps['!'] = true;
	// These unary operators are handled in ParsePrimary().
	UnaryOps['-'] = false;
	UnaryOps['&'] = false;
	UnaryOps['*'] = false;
	// Read the provided file.
	FileData = ReadFile(file_name);
	FileDataLength = (signed int) FileData.length();
	Preprocess(file_name); // run preprocessor to handle imports, etc.
	// Get first token.
	getNextToken();
	// Run main loop now.
	MainLoop();
	// Dump all generated code.
	TheFPM = 0;
	raw_fd_ostream ofp("out.ll", err, llvm::sys::fs::OpenFlags::F_None);
	if(verifyModule(*mod, &ofp)){
		mod->dump();
		Error("Module could not be verified.");
	}
	mod->dump();
	mod->print(ofp, NULL);
	if(ShouldOptimize){
		system("llc out.ll -filetype=obj -o out.o");
		system(("ld " + linker_options + " out.o -e _main -macosx_version_min 10.8 -o " + out_name).c_str());
	} else {
		fprintf(stderr, "Not compiling due to no optimizations.\n");
	}
	return 0;
}

int main(int argc, char** argv){
	if(argc < 2){
		fprintf(stderr, "Usage: %s [filename] [opt1]...[optn]\n", argv[0]);
		return 0;
	}
	for(int i = 1; i < argc; i++){
		std::string on = argv[i];
		if((on.substr(0, 2) == "-O") && (on.length() > 2)){
			int lvl = (int) (on[2] - '0');
			if(!lvl) ShouldOptimize = false;
			op_lvl = lvl;
		} else if(on == "-test"){
			return RunTests();
		} else if((on.substr(0, 2) == "-l") && (on.length() > 2)){
			linker_options += on + " ";
		}
	}
	return Compile(std::string(argv[1]));
}
























































