// Hayden Schindler
// CS 4301
// stage1

#include <stage2.h>
#include <iostream>
#include <fstream>
#include <string>
#include <map>
#include <ctime>
#include <cctype>
#include <iomanip>
#include <fstream>
#include <algorithm>
#include <cstdio>
#include <ctype.h>
#include <vector>
#include <locale>
#include <stack>
#include <cstring>

using namespace std;

Compiler::Compiler(char **argv)
{
   sourceFile.open(argv[1]);
	listingFile.open(argv[2]);
	objectFile.open(argv[3]);
}
// constructor
Compiler::~Compiler()
{
   sourceFile.close();
	listingFile.close();
	objectFile.close();
} 
// destructor

void Compiler::createListingHeader()
{
   time_t now = time(NULL);
   listingFile << "STAGE2:";
   listingFile << setw(21) << left << " Hayden Schindler";
   listingFile << right << ctime(&now) << endl;
   listingFile << left << setw(22) << "LINE NO." << right << "SOURCE STATEMENT" << endl << endl;
}
void Compiler::parser()
{
   nextChar();
   //ch must be initialized to the first character of the source file
   if (nextToken() != "program")
   {
      processError("keyword \"program\" expected");
   }
   //a call to nextToken() has two effects
   // (1) the variable, token, is assigned the value of the next token
   // (2) the next token is read from the source file in order to make
   // the assignment. The value returned by nextToken() is also
   // the next token.
   prog();
   //parser implements the grammar rules, calling first rule
}
void Compiler::createListingTrailer()
{
   listingFile << "\n" << left << setw(21) << "COMPILATION TERMINATED" << right << setw(7) << errorCount << " ERRORS ENCOUNTERED" << endl;
}

// Methods implementing the grammar productions
void Compiler::prog()
{
   if (token != "program")
   {
      processError("keyword \"program\" expected");
   }
   progStmt();
   
   if (token == "const")
   {
      consts();
   }
   if (token == "var")
   {
      vars();
   }
   if (token != "begin")
   {
      processError("keyword \"begin\" expected");
   }
   beginEndStmt();
   
   if (token[0] != END_OF_FILE)
   {
      processError("no text may follow \"end\"");
   }
} 

// stage 0, production 1
void Compiler::progStmt()
{
   string x;
   
   if (token != "program")
   {
      processError("keyword \"program\" expected");
   }
   x = nextToken();
   
   if (!isNonKeyId(x))
   {
      processError("program name expected");
   }
   if (nextToken() != ";")
   {
      processError("\";\" expected");
   }
   nextToken();
   code("program", x);
   insert(x,PROG_NAME,CONSTANT,x,NO,0);
}
// stage 0, production 2
void Compiler::consts()
{
   if (token != "const")
   {
      processError("keyword \"const\" expected");
   }
   if (!isNonKeyId(nextToken()))
   {
      processError("non-keyword identifier must follow \"const\"");
   }
   constStmts();
}
// stage 0, production 3
void Compiler::vars()
{
   if (token != "var")
   {
      processError("keyword \"var\" expected");
   }
   if (!isNonKeyId(nextToken()))
   { 
      processError("non-keyword identifier must follow \"var\"");
   }
	varStmts();
} 

// stage 0, production 4

int beginCount = 0;
void Compiler::beginEndStmt()
{
   if (token != "begin")
   {
      processError("keyword \"begin\" expected");
   }
   // EXEC_STMTS check after begin for stage1
   beginCount += 1;
   execStmts();
   
   if (token != "end")
   {
      processError("keyword \"end\" expected");
   }
   beginCount -= 1;
   
   nextToken();
   if (token == ";")
   {
      return;
   }
   // stage 2 ; revision
   if (token == "." && beginCount > 0)
   {
      processError("semicolon expected");
   }
   
   code("end", ".");
   nextToken();
} 
// stage 0, production 5
void Compiler::constStmts()
{
   string x,y;
   if (!isNonKeyId(token))
   {
      processError("non-keyword identifier expected");
   }
   x = token;
   
   if (nextToken() != "=")
   {   
      processError("\"=\" expected");
   }
   y = nextToken();
   
   if ((y != "+") && (y != "-") && (y != "not") && !isNonKeyId(y) && (y != "true") && (y != "false") && (!isInteger(y)))
   {
      processError("token to right of \"=\" illegal");
   }
   
   if (y == "+" || y == "-")
   {
      if (!isInteger(nextToken()))
      {
         processError("integer expected after sign");
      }
      y = y + token;
   }
   
   
   // Need to check for the non key Id and for the Lit after the = sign
   if (y == "not")
   {
      if (!isBoolean(whichValue(nextToken())))
      {
         processError("boolean expected after \"not\"");
      }
      if (token == "true")
      {
         y = "false";
      }
      else
      {
         y = "true";
      }
   }
   
   if (nextToken() != ";")
   {
      processError("semicolon expected");
   }
   if ((whichType(y) != INTEGER) && (whichType(y) != BOOLEAN))
   {
      processError("data type of token on the right-hand side must be INTEGER or BOOLEAN");
   }
   insert(x,whichType(y),CONSTANT,whichValue(y),YES,1);
   x = nextToken();
   
   if ((x != "begin") && (x != "var") && (!isNonKeyId(x)))
   {
      processError("non-keyword identifier, \"begin\", or \"var\" expected");
   }
   
   if (isNonKeyId(x))
   {
      constStmts();
   }
} 

// stage 0, production 6
void Compiler::varStmts()
{
   string x,y;
   
   storeTypes st;

   if (!isNonKeyId(token))
   {
      processError("non-keyword identifier expected");
   }
   x = ids();
   
   if (token != ":")
   {
      processError("\":\" expected");
   }
   
   nextToken();
   if ((token != "integer") && (token != "boolean"))
   {
      processError("illegal type follows \":\"");
   }
   y = token;
   
   nextToken();
   if (token != ";")
   {
      processError("semicolon expected");
   }
   
   if (y == "integer")
   {
      st = INTEGER;
   }
   
   if (y == "boolean")
   {
      st = BOOLEAN;
   }
   
   insert(x,st,VARIABLE,"",YES,1);
   
   nextToken();
   if ((token != "begin") && !isNonKeyId(token))
   {
      processError("non-keyword identifier or \"begin\" expected");
   }
   
   if (isNonKeyId(token))
   {
      varStmts();
   }
} 

// stage 0, production 7
string Compiler::ids()
{
   string temp,tempString;
   
   if (!isNonKeyId(token))
   {
      processError("non-keyword identifier expected");
   }
   tempString = token;
   temp = token;
   
   if (nextToken() == ",")
   {
      if (!isNonKeyId(nextToken()))
      {
         processError("non-keyword identifier expected");
      }
      tempString = temp + "," + ids();
   }
   return tempString;
}

// stage1, production 2
void Compiler::execStmts()
{
   nextToken();
	while (isNonKeyId(token) || token == "read" || token == "write" || token == "if" || token == "while" || token == "repeat" || token == ";" || token == "begin")
   {
      execStmt();
   }
   if (token == "until")
   {
      return;
   }
   // potential else
   if (token != "end")
   {
      processError("one of \";\", \"begin\", \"if\", \"read\", \"repeat\", \"while\", \"write\", \"end\", or \"until\" expected");
   }
}
void Compiler::execStmt()
{	
	if (isNonKeyId(token))
	{
      assignStmt();
	}
	
	else if (token == "read")
	{
      readStmt();
	}
	
	else if (token == "write")
	{
      writeStmt();
	}
   else if (token == "if")
   {
      ifStmt();
   }
   else if (token == "while")
   {
      whileStmt();
   }
   else if (token == "repeat")
   {
      repeatStmt();
   }
   else if (token == ";")
   {
      nullStmt();
   }
   else if (token == "begin")
   {
      beginEndStmt();
   }
} 

// stage 1, production 3
void Compiler::assignStmt()
{
	if (!isNonKeyId(token))
   {
      processError("non-keyword identifier expected");
   }
   pushOperand(token);
   
   nextToken();
   if (token != ":=")
   {
      processError("assignment operator expected");
   }
      
   pushOperator(token);
   express();
   
   if (token != ";")
   {
      processError("\";\" expected");
   }
   
   string y = popOperator();
   string z = popOperand();
   string a = popOperand();
   code(y, z, a);
   
   
} // stage 1, production 4


void Compiler::readStmt()
{
   // Check token contains "read"
	if (token != "read")
   {
      processError("read statement expected");
   }
   // check next token for "("
   if (nextToken() != "(")
   {
      processError("\"(\" expected");
   }
   
   nextToken();
   string idL = ids();
   
   if (token != ")")
   {
      processError("\")\" expected");
   }
   
   // create your readlist
   code("read", idL);
   
   if (nextToken() != ";")
   {
      processError("\";\" expected");
   }
 
} // stage 1, production 5
void Compiler::writeStmt()
{
   // Check token contains "write"
	if (token != "write")
   {
      processError("write statement expected");
   }
   // check next token for "("
   if (nextToken() != "(")
   {
      processError("\"(\" expected");
   }
   
   nextToken();
   string idL = ids();
   
   if (token != ")")
   {
      processError("\")\" expected");
   }
   
   // create your readlist
   code("write", idL);
   
   if (nextToken() != ";")
   {
      processError("\";\" expected");
   }  
} // stage 1, production 7

void Compiler::express()
{
   nextToken();
   if (token != "not" && !isBoolean(token) && !isInteger(token) && !isNonKeyId(token) && token != "(" && token != "+" && token != "-")
   {
      processError("expression expected");
   }

   term();
   expresses();
} // stage 1, production 9

void Compiler::expresses()
{
   if (token == "=" || token == "<>" || token == "<=" || token == ">=" || token == "<" || token == ">")
   {
      pushOperator(token);
      nextToken();
      term();
      string y = popOperator();
      string z = popOperand();
      string a = popOperand();
      code(y, z, a);
      expresses();
   }

} // stage 1, production 10

void Compiler::term()
{
   // same struct as express
   if (token != "not" && !isBoolean(token) && !isInteger(token) && !isNonKeyId(token) && token != "(" && token != "+" && token != "-")
   {
      processError("expression expected");
   }
   factor();
   terms();
} // stage 1, production 11

void Compiler::terms()
{
   if (token == "-" || token == "+" || token == "or")
   {
       pushOperator(token);
       nextToken();
       factor();
       string y = popOperator();
       string z = popOperand();
       string a = popOperand();
       code(y, z, a);
       terms();
   }

} // stage 1, production 12

void Compiler::factor()
{
   if (token != "not" && !isBoolean(token) && !isInteger(token) && !isNonKeyId(token) && token != "(" && token != "+" && token != "-")
   {
      processError("expression expected");
   }
   part();
   factors();

} // stage 1, production 13

void Compiler::factors()
{
   if (token == "*" || token == "div" || token == "mod" || token == "and")
   {
      pushOperator(token);
      nextToken();
      part();
      string y = popOperator();
      string z = popOperand();
      string a = popOperand();
      code(y, z, a);
      factors();
   }
 
} // stage 1, production 14
void Compiler::part()
{
   // 'not'
   if (token == "not")
   {
      nextToken();
      if (token == "(")
      {
         // if '(' EXPRESS ')'
         express();
         code("not", popOperand());
         
         if (token != ")")
         {
            processError("\")\" expected");
         }
         nextToken();
      }
      else if (isBoolean(token))
      {
         if (token == "true")
         {
            pushOperand("false");
            nextToken();
         }
         else
         {
            pushOperand("true");
            nextToken();
         }
      }
      else if (isNonKeyId(token))
      {
         code("not", token);
         nextToken();
      }
      else
      {
         processError("\"(\", boolean or non-key-id expected");
      }
   }
   // '+'
   else if (token == "+")
   {
      
      if (nextToken() == "(")
      {
         express();
         
         if (token != ")")
         {
            processError("\")\" expected");
         }
         nextToken();
      }
      else if (!isInteger(token) && !isNonKeyId(token))
      {
         processError("expected \"(\", integer or non-keyword-id; found " + token);
      }
      else
      {
         pushOperand(token);
         nextToken();
      }
   }
   // '-'
   else if (token == "-")
   {
      if (nextToken() == "(")
      {
         express();
         code("neg", popOperand());
         
         if (token != ")")
         {
            processError("\")\" expected");
         }
         nextToken();
         
      }
      else if (isInteger(token))
      {
         pushOperand("-" + token);
         nextToken();
      }
      
      else if (isNonKeyId(token))
      {
         code("neg", token);
         nextToken();
      }
      else
      {
         processError("expected \"(\", integer or non-keyword-id; found " + token);
      }
   }
   else if (isInteger(token) || isBoolean(token) || isNonKeyId(token))
   {
      pushOperand(token);
      nextToken();
   }
   else if (token == "(")
   {
      express();
      
      if (token != ")")
      {
         processError("\")\" expected");
      }

      nextToken();
   }
    else
    {
       processError("illegal use of keyword");
    }
} // stage 1, production 15

void Compiler::ifStmt()
{
   if (token != "if")
   {
      processError("if statement expected");
   }
   express();

   if (token != "then")
   {
      processError("then statement expected");
   }
   code("then", popOperand());
   
   if (token == "end")
   {
      processError("improper nesting");
   }
   nextToken();
   if (!isNonKeyId(token) && token != "read" && token != "write" && token != "if" && token != "while" && token != "repeat" && token != ";" && token != "begin")
   {
      processError("then clause may not be empty");
   }
   execStmt();
   elsePt();
   
}         // stage 2, production 3
void Compiler::elsePt()
{
   nextToken();
   if (token == "else")
   {
      code("else", popOperand());
      nextToken();
      execStmt();
   }
   code("post_if", popOperand());
}         // stage 2, production 4
void Compiler::whileStmt()
{
   if (token != "while")
   {
      processError("while statement expected");
   }
   code("while");
   express();

   if (token != "do")
   {
      processError("do statement expected");
   }
   code("do",popOperand());
   nextToken();
   execStmt();
   string x = popOperand();
   string y = popOperand();
   code("post_while", x, y);
}      // stage 2, production 5
void Compiler::repeatStmt()
{
   if (token != "repeat")
   {
      processError("repeat statement expected");
   }
   code("repeat");
   execStmts();
   
   
   if (token != "until")
   {
      processError("until statement expected");
   }
   express();
   string x = popOperand();
   string y = popOperand();
   code("until", x, y);
}     // stage 2, production 6
void Compiler::nullStmt()
{
   if (token != ";")
   {
      processError("null statment expected");
   }
   nextToken();
}       // stage 2, production 7

// relational operators????????????

// action routines for stage1
// Push routines include a check for stack overflow
// external name pushed onto the stack, but suggested inclass to push the index of the symbol table entry for name

void Compiler::pushOperand(string name)
{
   // if the name is a literal, and there's no entry for it create a symbol table entry
   // external name pushed onto the stack, but suggested inclass 
   // to push the index of the symbol table entry for name
   if (isLiteral(name))
   {
      if (symbolTable.count(name) == 0)
      {
         if (name == "true")
         {
             symbolTable.insert(pair<string, SymbolTableEntry>(name,SymbolTableEntry("TRUE",whichType(name),CONSTANT,name,YES,1)));
         }
         else if (name == "false")
         {
             symbolTable.insert(pair<string, SymbolTableEntry>(name,SymbolTableEntry("FALSE",whichType(name),CONSTANT,name,YES,1)));
         }
         else{
             symbolTable.insert(pair<string, SymbolTableEntry>(name,SymbolTableEntry(genInternalName(whichType(name)),whichType(name),CONSTANT,name,YES,1)));
         }
      }
   }
   operandStk.push(name);
}

void Compiler::pushOperator(string name)
{
   operatorStk.push(name);
}

string Compiler::popOperand()
{
   string temp;
   
   if (!operandStk.empty())
   {
      temp = operandStk.top();
      operandStk.pop();
   }
   else
   {
      processError("compiler error; operand stack underflow");
   }
   return temp;
}
string Compiler::popOperator()
{
   string temp;
   
   if (!operatorStk.empty())
   {
      temp = operatorStk.top();
      operatorStk.pop();
   }
   else
   {
      processError("compiler error; operator stack underflow");
   }
   return temp;
}
// Helper functions for the Pascallite lexicon
bool Compiler::isKeyword(string s) const
{
	if (s == "program" || s == "begin" || s == "end" || s == "var" || s == "const" || s == "integer" || s == "boolean" 
		|| s == "true" || s == "false" || s == "not" || s == "mod" || s == "div" || s == "and" || s == "or" || s == "read" || s == "write" || s == "if"
       || s == "then" || s == "else" || s == "while" || s == "do" || s == "repeat" || s == "until")
	{
		return true;
	}
	else
	{
		return false;
	}
} 
// determines if s is a keyword
bool Compiler::isSpecialSymbol(char c) const
{
	if (c == '=' || c == ':' || c == ',' || c == ';' || c == '.' || c == '+' || c == '-' || c == '.' || c == '(' || c == ')' || c == '*' || c == '<' || c == '>')
	{
		return true;
	}
	else
	{
		return false;
	}
} 
// determines if c is a special symbol
bool Compiler::isNonKeyId(string s) const
{
   string temp;
   if ((isSpecialSymbol(s[0])))
   {
      return false;
   }

   if (isalpha(s[0]))
   {
      for (uint i = 0; i <s.length(); i++)
      {
         if (isalnum(s[i]) || s[i] == '_')
         {
            temp += s[i];
         }
      }
      if (isKeyword(temp))
      {
         return false;
      }
   }
   return true;
}
// determines if s is a non_key_id
bool Compiler::isInteger(string s) const
{
   for (uint i = 0; i <= s.length()-1; i++)
   {
      if (s[0] == '+' || s[0] == '-')
      {
         i++;
      }
      if(!isdigit(s[i]))
      {
         return false;
      }
   }
   return true;
}   
// determines if s is an integer

bool Compiler::isBoolean(string s) const
{
	if (s == "true" || s == "false")
	{
		return true;
	}
	else
		return false;
} 
// determines if s is a boolean
bool Compiler::isLiteral(string s) const
{
	if (isInteger(s) || s == "false" || s == "true" || s == "not" || s == "+" || s == "-")
	{
		return true;
	}
	else
	{
		return false;
	}
} // determines if s is a literal

// Action routines
void Compiler::insert(string externalName, storeTypes inType, modes inMode,string inValue, allocation inAlloc, int inUnits)
{
   // create symbol table entry for each identifier in list of external names
   // Multiply inserted names are illegal 
   string name;
   uint LName = 0;
   
   while (LName < externalName.length())
   {
      name = "";
      while (name == "")
      {
         while (LName < externalName.length() && externalName[LName] != ',')
         {
            name = name + externalName[LName];
            LName = LName + 1;
         }
         
         LName += 1;
   
      if (!name.empty())
      {
         if (name.length() > 15)
         {
            name = name.substr(0,15);
         }
            if (symbolTable.count(name) > 0)
            {
               processError("multiple name definition");
            }
            else if (isKeyword(name) && (name != "true") && (name != "false"))
            {
               processError("illegal use of keyword");
            }
            else //create table entry
            {
               if (isupper(name[0]))
               {
                  symbolTable.insert(pair<string, SymbolTableEntry>(name,SymbolTableEntry(name,inType,inMode,inValue,inAlloc,inUnits)));
               }
               else
               {
                  //symbolTable[name]=(genInternalName(inType),inType,inMode,inValue,inAlloc,inUnits)
                  symbolTable.insert(pair<string, SymbolTableEntry>(name,SymbolTableEntry(genInternalName(inType),inType,inMode,inValue,inAlloc,inUnits)));
               }
            }
         }
      }
      if (symbolTable.size() > 256)
      {
         processError("symbol table cannot exceed 256");
      }
   }
}


storeTypes Compiler::whichType(string name)
{
   storeTypes dataType;
   
   if (isLiteral(name) == true)
   {
      if (isBoolean(name) == true)
      {
         dataType = BOOLEAN;
      }
      else
      {
         dataType =  INTEGER;
      }
   }
   else //name is an identifier and hopefully a constant
   {
      auto st = symbolTable.find(name);
      
      if (st != symbolTable.end())
      {
         dataType = (*st).second.getDataType();
      }
      else
      {
         processError("reference to undefined symbol " + name);
      }
   }
   return dataType;// tells which data type a name has
}

string Compiler::whichValue(string name)
{
   string value;
   auto it = symbolTable.find(name);
   
   if (isLiteral(name) == true)
   {
      value += name;
   }
   else 
   {
      if (it != symbolTable.end())
      {
         value = (*it).second.getValue();
      }
      //name is an identifier and hopefully a constant
      else
      {
         processError("reference to undefined symbol " + name);
      }
   }
   return value;
   
} 
// tells which value a name has
void Compiler::code(string op, string operand1, string operand2)
{
   if (op == "program")
   {
      emitPrologue(operand1);
   }
   else if (op == "end")
   {
      emitEpilogue();
   }
   else if (op == "read")
   {
      emitReadCode(operand1, operand2);
   }
   else if (op == "write")
   {
      emitWriteCode(operand1, operand2);
   }
   else if (op == "then")
   {
      emitThenCode(operand1, operand2);
   }
   else if (op == "else")
   {
      emitElseCode(operand1, operand2);
   }
   else if (op == "post_if")
   {
      emitPostIfCode(operand1, operand2);
   }
   else if (op == "while")
   {
      emitWhileCode(operand1, operand2);
   }
   else if (op == "do")
   {
      emitDoCode(operand1, operand2);
   }
   else if (op == "post_while")
   {
      emitPostWhileCode(operand1, operand2);
   }
   else if (op == "repeat")
   {
      emitRepeatCode(operand1, operand2);
   }
   else if (op == "until")
   {
      emitUntilCode(operand1, operand2);
   }
   else if (op == "else")
   {
      emitElseCode(operand1, operand2);
   }
   else if (op == "+")
   {
      emitAdditionCode(operand1, operand2);
   }
   else if (op == "-")
   {
      emitSubtractionCode(operand1, operand2);
   }
   else if (op == "neg")
   {
      emitNegationCode(operand1, operand2);
   }
   else if (op == "not")
   {
      emitNotCode(operand1, operand2);
   }
   else if (op == "*")
   {
      emitMultiplicationCode(operand1, operand2);
   }
   else if (op == "div")
   {
      emitDivisionCode(operand1, operand2);
   }
   else if (op == "mod")
   {
      emitModuloCode(operand1, operand2);
   }
   else if (op == "and")
   {
      emitAndCode(operand1, operand2);
   }
   else if (op == "or")
   {
      emitOrCode(operand1, operand2);
   }
   else if (op == "=")
   {
      emitEqualityCode(operand1, operand2);
   }
   else if (op == "<>")
   {
      emitInequalityCode(operand1, operand2);
   }
   else if (op == "<")
   {
      emitLessThanCode(operand1, operand2);
   }
   else if (op == "<=")
   {
      emitLessThanOrEqualToCode(operand1, operand2);
   }
   else if (op == ">")
   {
      emitGreaterThanCode(operand1, operand2);
   }
   else if (op == ">=")
   {
      emitGreaterThanOrEqualToCode(operand1, operand2);
   }
   else if (op == ":=")
   {
      emitAssignCode(operand1, operand2);
   }
   else
   {
      processError("compiler error since function code should not be called with illegal arguments");
   }
}

// Emit Functions
void Compiler::emit(string label, string instruction, string operands,
                    string comment)
{
   /*Turn on left justification in objectFile
   
   Output label in a field of width 8
   Output instruction in a field of width 8
   Output the operands in a field of width 24
   Output the comment*/
   objectFile << left;
   objectFile << setw(8) << label;
   objectFile << setw(8) << instruction;
   objectFile << setw(24) << operands;
   objectFile << comment << endl;
}
void Compiler::emitPrologue(string progName, string operand2)
{
   /*Output identifying comments at beginning of objectFile
   Output the %INCLUDE directives*/
   time_t now = time(NULL);
   objectFile << "; Hayden Schindler   " << ctime(&now);
   objectFile << "%INCLUDE \"Along32.inc\"" << endl << "%INCLUDE \"Macros_Along.inc\"\n";
   emit();
   emit("SECTION", ".text");
   emit("global", "_start", "", "; program " + progName);
   emit("\n_start:");
}
void Compiler::emitEpilogue(string operand1, string operand2)
{
   emit("","Exit", "{0}\n");
   emitStorage();
}
void Compiler::emitStorage()
{
   emit("SECTION", ".data");
   /*for those entries in the symbolTable that have
   an allocation of YES and a storage mode of CONSTANT
   { call emit to output a line to objectFile }*/
   for (auto table = symbolTable.begin(); table != symbolTable.end(); table++)
   { 
      string value;
      if (table->second.getAlloc() == YES && table->second.getMode() == CONSTANT)
      {
         if (table->second.getValue() == "true")
         {
             value = "-1";
         }
         else if (table->second.getValue() == "false")
         {
             value = "0";
         }
         else
         {
            value = table->second.getValue();
         }

            emit(table->second.getInternalName(), "dd", value, "; " + table->first);
      }   
    }
   emit("\nSECTION", " .bss");
   /*for those entries in the symbolTable that have
   an allocation of YES and a storage mode of VARIABLE
   { call emit to output a line to objectFile }*/
   for (auto table = symbolTable.begin(); table != symbolTable.end(); table++)
   {
      if (table->second.getAlloc() == YES && table->second.getMode() == VARIABLE)
      {
         emit(table->second.getInternalName(), "resd", "1" ,"; " + table->first);
      }
   }
}

// stage1 emit functions
void Compiler::emitReadCode(string operand, string operand2)
{
    string name;
    map<string, SymbolTableEntry>::iterator itr;
    
    while(operand != "")
    {
        name = "";

        while (operand != "" && operand[0] != ',')
        {
            name += operand[0];
            operand.erase(0,1);
        }
        while(name.length() > 15)
            name = name.substr(0,15);
        
        if(operand[0] == ',')
         {
            operand.erase(0,1);
         }

        itr = symbolTable.find(name);
        
        if(itr == symbolTable.end())
         {
            processError("reference to undefined symbol");
         }
        if(itr->second.getDataType() != INTEGER)
         {
            processError("can't read variables of this type");
         }
        if(itr->second.getMode() != VARIABLE)
         {
            processError("attempting to read to a read-only location "" + name + """);
         }
        
        emit("", "call", "ReadInt", "; read int; value placed in eax");
        emit("", "mov", "[" + itr->second.getInternalName() + "],eax", "; store eax at " + name);
        contentsOfAReg = name;
    }
}
void Compiler::emitWriteCode(string operand, string operand2)
{
      string name;
      map<string, SymbolTableEntry>::iterator itr;
      
      while(operand != "")
      {
         name = "";

        while (operand != "" && operand[0] != ',')
        {
            name += operand[0];
            operand.erase(0,1);
        }
        while(name.length() > 15)
            name = name.substr(0,15);
        
        if(operand[0] == ',')
         {
            operand.erase(0,1);
         }

        itr = symbolTable.find(name);
        
        if(itr == symbolTable.end())
         {
            processError("reference to undefined symbol");
         }
         if (contentsOfAReg != name)
         {
            emit("", "mov","eax,[" + itr->second.getInternalName() + "]", "; load " + name + " in eax");
            contentsOfAReg = name;
         }
         if (itr->second.getDataType() == INTEGER || itr->second.getDataType() == BOOLEAN)
         {
            emit("", "call", "WriteInt", "; write int in eax to standard out");
         }
         emit("", "call", "Crlf", "; write \\r\\n to standard out");
      }
}
void Compiler::emitAssignCode(string operand1, string operand2)
{
   if (whichType(operand1) != whichType(operand2))
   {
      processError("incompatible types for operator \':=\'");
   }
   else if (symbolTable.at(operand2).getMode() != VARIABLE)
   {
      processError("symbol on the left-hand side of assigment must have the storage mode of VARIABLE");
   }
   else if (operand1 == operand2)
   {
      return;
   }
   else if (contentsOfAReg != operand1)
   {
      emit("", "mov","eax,[" + symbolTable.at(operand1).getInternalName() + "]", "; AReg = " + operand1);
   }
   emit("", "mov", "[" + symbolTable.at(operand2).getInternalName() + "],eax", "; " + operand2 + " = AReg" );
   contentsOfAReg = operand2;
   
   if (isTemporary(operand1))
   {
      freeTemp();
   }
}         // op2 = op1

void Compiler::emitAdditionCode(string operand1, string operand2)
{
	operand1 = operand1.substr(0,15);
	operand2 = operand2.substr(0,15);
   
   if (whichType(operand1) != INTEGER || whichType(operand2) != INTEGER)
   {
      processError("binary \'+\' requires integer operands");
   }
   if (symbolTable.find(contentsOfAReg) != symbolTable.end() && isTemporary(contentsOfAReg) && contentsOfAReg != operand1 && contentsOfAReg != operand2)
   {
      emit("", "mov","[" + symbolTable.at(contentsOfAReg).getInternalName() + "]" + ",eax", "; deassign AReg");
	  
	  // if symbolTableName name = contentsOfAReg

      symbolTable.at(contentsOfAReg).setAlloc(YES);
      contentsOfAReg = "";
   }
   if (symbolTable.find(contentsOfAReg) != symbolTable.end() && !isTemporary(contentsOfAReg) && contentsOfAReg != operand1 && contentsOfAReg != operand2)
   {
	   contentsOfAReg = "";
   }
   if (contentsOfAReg != operand1 && contentsOfAReg != operand2)
   {
	   emit("", "mov", "eax,[" + symbolTable.at(operand2).getInternalName() + "]", "; AReg = " + operand2);
   }
   
   // emit code to perform register-memory addition
   if (contentsOfAReg == operand1)
   {
		emit("", "add", "eax,[" + symbolTable.at(operand2).getInternalName() + "]", "; AReg = " + operand1 + " + " + operand2);
   }
   else
   {
	   emit("", "add", "eax,[" + symbolTable.at(operand1).getInternalName() + "]", "; AReg = " + operand2 + " + " + operand1);
   }
   
   // deassign all the temporaries involved and free those names for reuse
   if (isTemporary(operand1))
   {
      freeTemp();
   }
   
   if (isTemporary(operand2))
   {
	   freeTemp();
   }
   
   // get the next available temp and store in the A register
   contentsOfAReg = getTemp();
   symbolTable.at(contentsOfAReg).setDataType(INTEGER);
   
   // Push the name of the result onto the stack
   pushOperand(contentsOfAReg);
   
}       // op2 +  op1

void Compiler::emitSubtractionCode(string operand1, string operand2)
{
   operand1 = operand1.substr(0,15);
	operand2 = operand2.substr(0,15);
   
   if (whichType(operand1) != INTEGER || whichType(operand2) != INTEGER)
   {
      processError("illegal type");
   }
   if (symbolTable.find(contentsOfAReg) != symbolTable.end() && isTemporary(contentsOfAReg) && contentsOfAReg != operand1 && contentsOfAReg != operand2)
   {
      emit("", "mov","[" + contentsOfAReg + "]" + ",eax", "; deassign AReg");
	  
	  // if symbolTableName name = contentsOfAReg

      symbolTable.at(contentsOfAReg).setAlloc(YES);
      contentsOfAReg = "";
   }
   if (symbolTable.find(contentsOfAReg) != symbolTable.end() && !isTemporary(contentsOfAReg) && contentsOfAReg != operand1 && contentsOfAReg != operand2)
   {
	   contentsOfAReg = "";
   }
   if (contentsOfAReg != operand1 || contentsOfAReg != operand2)
   {
	   emit("", "mov", "eax,[" + symbolTable.at(operand2).getInternalName() + "]", "; AReg = " + operand2);
   }
   
   // emit code to perform register-memory addition
   if (contentsOfAReg == operand1)
   {
		emit("", "sub", "eax,[" + symbolTable.at(operand2).getInternalName() + "]", "; AReg = " + operand2 + " - " + operand1);
   }
   else
   {
	   emit("", "sub", "eax,[" + symbolTable.at(operand1).getInternalName() + "]", "; AReg = " + operand2 + " - " + operand1);
   }
   
   // deassign all the temporaries involved and free those names for reuse
   if (isTemporary(operand1))
   {
      freeTemp();
   }
   
   if (isTemporary(operand2))
   {
	   freeTemp();
   }
   
   // get the next available temp and store in the A register
   contentsOfAReg = getTemp();
   symbolTable.at(contentsOfAReg).setDataType(INTEGER);
   
   // Push the name of the result onto the stack
   pushOperand(contentsOfAReg);
}    
// op2 -  op1
void Compiler::emitMultiplicationCode(string operand1, string operand2)
{
   operand1 = operand1.substr(0,15);
	operand2 = operand2.substr(0,15);
	
   if (whichType(operand1) != INTEGER || whichType(operand2) != INTEGER)
   {
      processError("illegal type");
   }
   if (symbolTable.find(contentsOfAReg) != symbolTable.end() && isTemporary(contentsOfAReg) && contentsOfAReg != operand1 && contentsOfAReg != operand2)
   {
      emit("", "mov","[" + contentsOfAReg + "]" + ",eax", "; ");
	  // if symbolTableName name = contentsOfAReg
      symbolTable.at(contentsOfAReg).setAlloc(YES);
      contentsOfAReg = "";
   }
   if (contentsOfAReg != operand1 && contentsOfAReg != operand2)
   {
      emit("", "mov", "eax,[" + symbolTable.at(operand2).getInternalName() + "]", "; AReg = " + operand2);
      contentsOfAReg = operand2;
   }
   if (contentsOfAReg != operand1)
   {
      emit("", "imul", "dword [" + symbolTable.at(operand1).getInternalName() + "]", "; AReg = " + contentsOfAReg + " * " + operand1);
   }
   else
   {
      emit("", "imul", "dword [" + symbolTable.at(operand2).getInternalName() + "]", "; AReg = " + contentsOfAReg + " * " + operand2);
   }
	
   // deassign all the temporaries involved and free those names for reuse
   if (isTemporary(operand1))
   {
      freeTemp();
   }
   
   if (isTemporary(operand2))
   {
	   freeTemp();
   }
   
   // get the next available temp and store in the A register
   contentsOfAReg = getTemp();
   symbolTable.at(contentsOfAReg).setDataType(INTEGER);
   
   // Push the name of the result onto the stack
   pushOperand(contentsOfAReg);
   	
} 
// op2 *  op1
void Compiler::emitDivisionCode(string operand1, string operand2)
{
	operand1 = operand1.substr(0,15);
	operand2 = operand2.substr(0,15);
	
   if (whichType(operand1) != INTEGER || whichType(operand2) != INTEGER)
   {
      processError("illegal type");
   }
   
   if (symbolTable.find(contentsOfAReg) != symbolTable.end() && isTemporary(contentsOfAReg) && contentsOfAReg != operand1 && contentsOfAReg != operand2)
   {
      emit("", "mov","[" + contentsOfAReg + "]" + ",eax", "AReg = " + contentsOfAReg);
	  
	  // if symbolTableName name = contentsOfAReg

      symbolTable.at(contentsOfAReg).setAlloc(YES);
      contentsOfAReg = "";
   }
   if (!isTemporary(contentsOfAReg) && contentsOfAReg != operand2)
   {
	   contentsOfAReg = "";
   }
   if (contentsOfAReg != operand2)
   {
	   emit("", "mov", "eax,[" + symbolTable.at(operand2).getInternalName() + "]", "; AReg = " + operand2);
   }
	emit("", "cdq", "", "; sign extend dividend from eax to edx:eax");
	emit("", "idiv", "dword [" + contentsOfAReg + "]", "; AReg = " + operand2 + " div " + contentsOfAReg);
	
	// deassign all the temporaries involved and free those names for reuse
   if (isTemporary(operand1))
   {
      freeTemp();
   }
   
   if (isTemporary(operand2))
   {
	   freeTemp();
   }
   
   // get the next available temp and store in the A register
   contentsOfAReg = getTemp();
   symbolTable.at(contentsOfAReg).setDataType(INTEGER);
   
   // Push the name of the result onto the stack
   pushOperand(contentsOfAReg);
}       // op2 /  op1

void Compiler::emitModuloCode(string operand1, string operand2)
{
	operand1 = operand1.substr(0,15);
	operand2 = operand2.substr(0,15);
	
   if (whichType(operand1) != INTEGER || whichType(operand2) != INTEGER)
   {
      processError("illegal type");
   }
   
   if (symbolTable.find(contentsOfAReg) != symbolTable.end() && isTemporary(contentsOfAReg) && contentsOfAReg != operand1 && contentsOfAReg != operand2)
   {
      emit("", "mov","[" + contentsOfAReg + "]" + ",eax", "; deassign AReg");
	  
	  // if symbolTableName name = contentsOfAReg
      symbolTable.at(contentsOfAReg).setAlloc(YES);
      contentsOfAReg = "";
   }
   if (symbolTable.find(contentsOfAReg) != symbolTable.end() && !isTemporary(contentsOfAReg) && contentsOfAReg != operand2)
   {
	   contentsOfAReg = "";
   }
   if (contentsOfAReg != operand2)
   {
	   emit("", "mov", "eax,[" + symbolTable.at(operand2).getInternalName() + "]", "; AReg = " + operand2);
   }
	emit("", "cdq", "", "; sign extend dividend from eax to edx:eax");
	emit("", "idiv", "dword [" + symbolTable.at(operand1).getInternalName() + "]", "; AReg = " + operand2 + " div " + operand1);
   emit("", "xchg", "eax,edx", "; exchange quotient and remainder");
	
	// deassign all the temporaries involved and free those names for reuse
   if (isTemporary(operand1))
   {
      freeTemp();
   }
   
   if (isTemporary(operand2))
   {
	   freeTemp();
   }
   
   // get the next available temp and store in the A register
   contentsOfAReg = getTemp();
   symbolTable.at(contentsOfAReg).setDataType(INTEGER);
   
   // Push the name of the result onto the stack
   pushOperand(contentsOfAReg);
}         // op2 %  op1
void Compiler::emitNegationCode(string operand1, string operand2)
{
   operand1 = operand1.substr(0,15);
	
   if (whichType(operand1) != INTEGER)
   {
      processError("illegal type");
   }
   if (contentsOfAReg != operand1)
   {
	   emit("", "mov","[" + symbolTable.at(operand1).getInternalName() + "]" + ",eax", "mov contents of " + symbolTable.at(operand1).getInternalName() + "to the eax register");
   }
   emit("", "neg", "eax", "; AReg = -AReg");
   
   // deassign all the temporaries involved and free those names for reuse
   if (isTemporary(operand1))
   {
      freeTemp();
   }
   
   // get the next available temp and store in the A register
   contentsOfAReg = getTemp();
   symbolTable.at(contentsOfAReg).setDataType(INTEGER);
   
   // Push the name of the result onto the stack
   pushOperand(contentsOfAReg);
}           // -op1
void Compiler::emitNotCode(string operand1, string operand2)
{
   operand1 = operand1.substr(0,15);
	
   if (whichType(operand1) != BOOLEAN)
   {
      processError("incompatible types, BOOLEAN required");
   }
   if (contentsOfAReg != operand1)
   {
	   emit("", "mov", "eax,[" + symbolTable.at(operand1).getInternalName() + "]", "; AReg = " + operand1);
	   contentsOfAReg = operand2;
   }
   emit("", "not", "eax", "; AReg = !AReg");
   // deassign all the temporaries involved and free those names for reuse
   if (isTemporary(operand1))
   {
      freeTemp();
   }
   
   if (isTemporary(operand2))
   {
	   freeTemp();
   }
   
   // get the next available temp and store in the A register
   contentsOfAReg = getTemp();
   symbolTable.at(contentsOfAReg).setDataType(BOOLEAN);
   
   // Push the name of the result onto the stack
   pushOperand(contentsOfAReg);
}                // !op1
void Compiler::emitAndCode(string operand1, string operand2)
{
   operand1 = operand1.substr(0,15);
   operand2 = operand2.substr(0,15);
	
   if (whichType(operand1) != BOOLEAN || whichType(operand2) != BOOLEAN)
   {
      processError("binary \'and\' requires boolean operands");
   }
   if (symbolTable.find(contentsOfAReg) != symbolTable.end() && isTemporary(contentsOfAReg) && contentsOfAReg != operand1 && contentsOfAReg != operand2)
   {
     emit("", "mov","[" + contentsOfAReg + "]" + ",eax", "; AReg = " + operand2);
	  
	  // change contentsofAReg allocation in the symbol table to YES and deassign the regsiter

      symbolTable.at(contentsOfAReg).setAlloc(YES);
      contentsOfAReg = "";
   }
   if (!isTemporary(contentsOfAReg) && contentsOfAReg != operand2)
   {
	   contentsOfAReg = "";
   }
   if (contentsOfAReg != operand1 && contentsOfAReg != operand2)
   {
	   emit("", "mov", "eax,[" + symbolTable.at(operand2).getInternalName() + "]", "; AReg = " + operand2);
	   contentsOfAReg = operand2;
   }
   if (contentsOfAReg == operand2)
   {
      emit("", "and", "eax,[" + symbolTable.at(operand1).getInternalName() + "]", "; AReg = " + operand2 + " and " + operand1);
   }
   else
   {
      emit("", "and", "eax,[" + symbolTable.at(operand2).getInternalName() + "]", "; AReg = " + operand1 + " and " + operand2);
   }
   // deassign all the temporaries involved and free those names for reuse
   if (isTemporary(operand1))
   {
      freeTemp();
   }
   
   if (isTemporary(operand2))
   {
	   freeTemp();
   }
   
   // get the next available temp and store in the A register
   contentsOfAReg = getTemp();
   symbolTable.at(contentsOfAReg).setDataType(BOOLEAN);
   
   // Push the name of the result onto the stack
   pushOperand(contentsOfAReg);
   
}            // op2 && op1
void Compiler::emitOrCode(string operand1, string operand2)
{
   operand1 = operand1.substr(0,15);
	operand2 = operand2.substr(0,15);
	
   if (whichType(operand1) != BOOLEAN || whichType(operand2) != BOOLEAN)
   {
      processError("incompatible types");
   }
   if (symbolTable.find(contentsOfAReg) != symbolTable.end() && isTemporary(contentsOfAReg) && contentsOfAReg != operand1 && contentsOfAReg != operand2)
   {
     emit("", "mov","[" + contentsOfAReg + "]" + ",eax", "; deassign AReg");
	  
	  // if symbolTableName name = contentsOfAReg

      symbolTable.at(contentsOfAReg).setAlloc(YES);
      contentsOfAReg = "";
   }
   if (symbolTable.find(contentsOfAReg) != symbolTable.end() && !isTemporary(contentsOfAReg) && contentsOfAReg != operand2)
   {
	   contentsOfAReg = "";
   }
   if (contentsOfAReg != operand1 && contentsOfAReg != operand2)
   {
	   emit("", "mov", "eax,[" + symbolTable.at(operand2).getInternalName() + "]", "; AReg = " + operand2);
      contentsOfAReg = operand2;
   }
   if (contentsOfAReg == operand2)
   {
      emit("", "or", "eax,[" + symbolTable.at(operand1).getInternalName() + "]", "; AReg = " + operand2 + " or " + operand1);
   }
   else
   {
      emit("", "or", "eax,[" + symbolTable.at(operand2).getInternalName() + "]", "; AReg = " + operand1 + " or " + operand2);
   }
   // deassign all the temporaries involved and free those names for reuse
   if (isTemporary(operand1))
   {
      freeTemp();
   }
   
   if (isTemporary(operand2))
   {
	   freeTemp();
   }
   
   // get the next available temp and store in the A register
   contentsOfAReg = getTemp();
   symbolTable.at(contentsOfAReg).setDataType(BOOLEAN);
   
   // Push the name of the result onto the stack
   pushOperand(contentsOfAReg);
   
}             // op2 || op1
void Compiler::emitEqualityCode(string operand1, string operand2)
{
   operand1 = operand1.substr(0,15);
	operand2 = operand2.substr(0,15);
	
   if (whichType(operand1) != whichType(operand2))
   {
      processError("incompatible types");
   }
   if (symbolTable.find(contentsOfAReg) != symbolTable.end() && isTemporary(contentsOfAReg) && contentsOfAReg != operand1 && contentsOfAReg != operand2)
   {
      emit("", "mov", "[" + contentsOfAReg + "],eax", "; deassign AReg");
	  
	  // if symbolTableName name = contentsOfAReg

      symbolTable.at(contentsOfAReg).setAlloc(YES);
      contentsOfAReg = "";
   }
   if (symbolTable.find(contentsOfAReg) != symbolTable.end() && !isTemporary(contentsOfAReg) && contentsOfAReg != operand1 && contentsOfAReg != operand2)
   {
	   contentsOfAReg = "";
   }
   if (contentsOfAReg != operand1 && contentsOfAReg != operand2)
   {
	   emit("", "mov", "eax,[" + symbolTable.at(operand2).getInternalName() + "]", "; AReg = " + operand2);
   }
   emit("", "cmp", "eax,[" + symbolTable.at(operand1).getInternalName() + "]", "; compare " + operand2 + " and " + operand1);
   string labelCountFirst = getLabel();
   emit("", "je", "." + labelCountFirst, "; if " + operand2 + " = " + operand1 + " then jump to set eax to TRUE");
   emit("", "mov", "eax,[FALSE]", "; else set eax to FALSE");
   // name,SymbolTableEntry(genInternalName(inType),inType,inMode,inValue,inAlloc,inUnits
   symbolTable.insert(pair<string, SymbolTableEntry>("false",SymbolTableEntry("FALSE",BOOLEAN,CONSTANT,whichValue("false"),YES,1)));
   string labelCountSecond = getLabel();
   emit("", "jmp", "." + labelCountSecond, "; unconditionally jump");
   emit("." + labelCountFirst + ":", "", "", "");
   emit("", "mov", "eax,[TRUE]", "; set eax to TRUE");
   symbolTable.insert(pair<string, SymbolTableEntry>("true",SymbolTableEntry("TRUE",BOOLEAN,CONSTANT,whichValue("true"),YES,1)));
   emit("." + labelCountSecond + ":", "", "", "");
   
   // deassign all the temporaries involved and free those names for reuse
   if (isTemporary(operand1))
   {
      freeTemp();
   }
   
   if (isTemporary(operand2))
   {
	   freeTemp();
   }
   
   // get the next available temp and store in the A register
   contentsOfAReg = getTemp();
   symbolTable.at(contentsOfAReg).setDataType(BOOLEAN);
   
   // Push the name of the result onto the stack
   pushOperand(contentsOfAReg);
   
}       // op2 == op1
void Compiler::emitInequalityCode(string operand1, string operand2)
{
   operand1 = operand1.substr(0,15);
	operand2 = operand2.substr(0,15);
	
   if (whichType(operand1) != whichType(operand2))
   {
      processError("incompatible types");
   }
   if (symbolTable.find(contentsOfAReg) != symbolTable.end() &&isTemporary(contentsOfAReg) && contentsOfAReg != operand1 && contentsOfAReg != operand2)
   {
      emit("", "mov", "[" + contentsOfAReg + "]" + ",eax", "; deassign AReg");
	  
	  // if symbolTableName name = contentsOfAReg

      symbolTable.at(contentsOfAReg).setAlloc(YES);
      contentsOfAReg = "";
   }
   if (symbolTable.find(contentsOfAReg) != symbolTable.end() && !isTemporary(contentsOfAReg) && contentsOfAReg != operand1 && contentsOfAReg != operand2)
   {
	   contentsOfAReg = "";
   }
   if (contentsOfAReg != operand1 && contentsOfAReg != operand2)
   {
	   emit("", "mov", "eax,[" + symbolTable.at(operand2).getInternalName() + "]", "; AReg = " + operand2);
   }
   emit("", "cmp", "eax,[" + symbolTable.at(operand1).getInternalName() + "]", "; compare " + operand2 + " and " + operand1);
   string labelCountFirst = getLabel();
   emit("", "jne", "." + labelCountFirst, "; if " + operand2 + " <> " + operand1 + " then jump to set eax to TRUE");
   emit("", "mov", "eax,[FALSE]", "; else set eax to FALSE");
   // name,SymbolTableEntry(genInternalName(inType),inType,inMode,inValue,inAlloc,inUnits
   symbolTable.insert(pair<string, SymbolTableEntry>("false",SymbolTableEntry("FALSE",BOOLEAN,CONSTANT,whichValue("false"),YES,1)));
   string labelCountSecond = getLabel();
   emit("", "jmp", "." + labelCountSecond, "; unconditionally jump");
   emit("." + labelCountFirst + ":", "", "", "");
   emit("", "mov", "eax,[TRUE]", "; set eax to TRUE");
   symbolTable.insert(pair<string, SymbolTableEntry>("true",SymbolTableEntry("TRUE",BOOLEAN,CONSTANT,whichValue("true"),YES,1)));
   emit("." + labelCountSecond + ":", "", "", "");
   
   // deassign all the temporaries involved and free those names for reuse
   if (isTemporary(operand1))
   {
      freeTemp();
   }
   
   if (isTemporary(operand2))
   {
	   freeTemp();
   }
   
   // get the next available temp and store in the A register
   contentsOfAReg = getTemp();
   symbolTable.at(contentsOfAReg).setDataType(BOOLEAN);
   
   // Push the name of the result onto the stack
   pushOperand(contentsOfAReg);
}     // op2 != op1
void Compiler::emitLessThanCode(string operand1, string operand2)
{
   operand1 = operand1.substr(0,15);
	operand2 = operand2.substr(0,15);
	
   if (whichType(operand1) != whichType(operand2))
   {
      processError("incompatible types");
   }
   if (symbolTable.find(contentsOfAReg) != symbolTable.end() && isTemporary(contentsOfAReg) && contentsOfAReg != operand1 && contentsOfAReg != operand2)
   {
      emit("", "mov", "[" + contentsOfAReg + "]" + ",eax", "; deassign AReg");
	  
	  // if symbolTableName name = contentsOfAReg

      symbolTable.at(contentsOfAReg).setAlloc(YES);
      contentsOfAReg = "";
   }
   if (symbolTable.find(contentsOfAReg) != symbolTable.end() && !isTemporary(contentsOfAReg) && contentsOfAReg != operand1 && contentsOfAReg != operand2)
   {
	   contentsOfAReg = "";
   }
   if (contentsOfAReg != operand2)
   {
	   emit("", "mov", "eax,[" + symbolTable.at(operand2).getInternalName() + "]", "; AReg = " + operand2);
   }
   emit("", "cmp", "eax,[" + symbolTable.at(operand1).getInternalName() + "]", "; compare " + operand2 + " and " + operand1);
   string labelCountFirst = getLabel();
   emit("", "jl", "." + labelCountFirst, "; if " + operand2 + " < " + operand1 + " then jump to set eax to TRUE");
   emit("", "mov", "eax,[FALSE]", "; else set eax to FALSE");
   // name,SymbolTableEntry(genInternalName(inType),inType,inMode,inValue,inAlloc,inUnits
   symbolTable.insert(pair<string, SymbolTableEntry>("false",SymbolTableEntry("FALSE",BOOLEAN,CONSTANT,whichValue("false"),YES,1)));
   string labelCountSecond = getLabel();
   emit("", "jmp", "." + labelCountSecond, "; unconditionally jump");
   emit("." + labelCountFirst + ":", "", "", "");
   emit("", "mov", "eax,[TRUE]", "; set eax to TRUE");
   symbolTable.insert(pair<string, SymbolTableEntry>("true",SymbolTableEntry("TRUE",BOOLEAN,CONSTANT,whichValue("true"),YES,1)));
   emit("." + labelCountSecond + ":", "", "", "");
   
   // deassign all the temporaries involved and free those names for reuse
   if (isTemporary(operand1))
   {
      freeTemp();
   }
   
   if (isTemporary(operand2))
   {
	   freeTemp();
   }
   
   // get the next available temp and store in the A register
   contentsOfAReg = getTemp();
   symbolTable.at(contentsOfAReg).setDataType(BOOLEAN);
   
   // Push the name of the result onto the stack
   pushOperand(contentsOfAReg);
}       // op2 <  op1
void Compiler::emitLessThanOrEqualToCode(string operand1, string operand2)
{
   operand1 = operand1.substr(0,15);
	operand2 = operand2.substr(0,15);
	
   if (whichType(operand1) != whichType(operand2))
   {
      processError("incompatible types");
   }
   if (symbolTable.find(contentsOfAReg) != symbolTable.end() && isTemporary(contentsOfAReg) && contentsOfAReg != operand1 && contentsOfAReg != operand2)
   {
      emit("", "mov", "eax,[" + contentsOfAReg + "]", "; deassign AReg");
	  
	  // if symbolTableName name = contentsOfAReg

      symbolTable.at(contentsOfAReg).setAlloc(YES);
      contentsOfAReg = "";
   }
   if (symbolTable.find(contentsOfAReg) != symbolTable.end() && !isTemporary(contentsOfAReg) && contentsOfAReg != operand1 && contentsOfAReg != operand2)
   {
	   contentsOfAReg = "";
   }
   if (contentsOfAReg != operand1 && contentsOfAReg != operand2)
   {
	   emit("", "mov", "eax,[" + symbolTable.at(operand2).getInternalName() + "]", "; AReg = " + operand2);
   }
   emit("", "cmp", "eax,[" + symbolTable.at(operand1).getInternalName() + "]", "; compare " + operand2 + " and " + operand1);
   string labelCountFirst = getLabel();
   emit("", "jle", "." + labelCountFirst, "; if " + operand1 + " <= " + operand2 + " then jump to set eax to TRUE");
   emit("", "mov", "eax,[FALSE]", "; else set eax to FALSE");
   // name,SymbolTableEntry(genInternalName(inType),inType,inMode,inValue,inAlloc,inUnits
   symbolTable.insert(pair<string, SymbolTableEntry>("false",SymbolTableEntry("FALSE",BOOLEAN,CONSTANT,whichValue("false"),YES,1)));
   string labelCountSecond = getLabel();
   emit("", "jmp", "." + labelCountSecond, "; unconditionally jump");
   emit("." + labelCountFirst + ":", "", "", "");
   emit("", "mov", "eax,[TRUE]", "; set eax to TRUE");
   symbolTable.insert(pair<string, SymbolTableEntry>("true",SymbolTableEntry("TRUE",BOOLEAN,CONSTANT,whichValue("true"),YES,1)));
   emit("." + labelCountSecond + ":", "", "", "");
   
   // deassign all the temporaries involved and free those names for reuse
   if (isTemporary(operand1))
   {
      freeTemp();
   }
   
   if (isTemporary(operand2))
   {
	   freeTemp();
   }
   
   // get the next available temp and store in the A register
   contentsOfAReg = getTemp();
   symbolTable.at(contentsOfAReg).setDataType(BOOLEAN);
   
   // Push the name of the result onto the stack
   pushOperand(contentsOfAReg);
} // op2 <= op1
void Compiler::emitGreaterThanCode(string operand1, string operand2)
{
   operand1 = operand1.substr(0,15);
	operand2 = operand2.substr(0,15);
	
   if (whichType(operand1) != whichType(operand2))
   {
      processError("incompatible types");
   }
   if (symbolTable.find(contentsOfAReg) != symbolTable.end() && isTemporary(contentsOfAReg) && contentsOfAReg != operand1 && contentsOfAReg != operand2)
   {
      emit("", "mov", "[" + contentsOfAReg + "],eax", "; deassign AReg");
	  
	  // if symbolTableName name = contentsOfAReg

      symbolTable.at(contentsOfAReg).setAlloc(YES);
      contentsOfAReg = "";
   }
   if (symbolTable.find(contentsOfAReg) != symbolTable.end() && !isTemporary(contentsOfAReg) && contentsOfAReg != operand1 && contentsOfAReg != operand2)
   {
	   contentsOfAReg = "";
   }
   if (contentsOfAReg != operand1 && contentsOfAReg != operand2)
   {
	   emit("", "mov", "eax,[" + symbolTable.at(operand2).getInternalName() + "]", "; AReg = " + operand2);
   }
   emit("", "cmp", "eax,[" + symbolTable.at(operand1).getInternalName() + "]", "; compare " + operand2 + " and " + operand1);
   string labelCountFirst = getLabel();
   emit("", "jg", "." + labelCountFirst, "; if " + operand2 + " > " + operand1 + " then jump to set eax to TRUE");
   emit("", "mov", "eax,[FALSE]", "; else set eax to FALSE");
   // name,SymbolTableEntry(genInternalName(inType),inType,inMode,inValue,inAlloc,inUnits
   symbolTable.insert(pair<string, SymbolTableEntry>("false",SymbolTableEntry("FALSE",BOOLEAN,CONSTANT,whichValue("false"),YES,1)));
   string labelCountSecond = getLabel();
   emit("", "jmp", "." + labelCountSecond, "; unconditionally jump");
   emit("." + labelCountFirst + ":", "", "", "");
   emit("", "mov", "eax,[TRUE]", "; set eax to TRUE");
   symbolTable.insert(pair<string, SymbolTableEntry>("true",SymbolTableEntry("TRUE",BOOLEAN,CONSTANT,whichValue("true"),YES,1)));
   emit("." + labelCountSecond + ":", "", "", "");
   
   // deassign all the temporaries involved and free those names for reuse
   if (isTemporary(operand1))
   {
      freeTemp();
   }
   
   if (isTemporary(operand2))
   {
	   freeTemp();
   }
   
   // get the next available temp and store in the A register
   contentsOfAReg = getTemp();
   symbolTable.at(contentsOfAReg).setDataType(BOOLEAN);
   
   // Push the name of the result onto the stack
   pushOperand(contentsOfAReg);
}   // op2 >  op1
void Compiler::emitGreaterThanOrEqualToCode(string operand1, string operand2)
{
   operand1 = operand1.substr(0,15);
	operand2 = operand2.substr(0,15);
	
   if (whichType(operand1) != whichType(operand2))
   {
      processError("incompatible types");
   }
   if (symbolTable.find(contentsOfAReg) != symbolTable.end() && isTemporary(contentsOfAReg) && contentsOfAReg != operand1 && contentsOfAReg != operand2)
   {
      emit("", "mov", "eax,[" + contentsOfAReg + "]", "; deassign AReg");
	  
	  // if symbolTableName name = contentsOfAReg

      symbolTable.at(contentsOfAReg).setAlloc(YES);
      contentsOfAReg = "";
   }
   if (symbolTable.find(contentsOfAReg) != symbolTable.end() && !isTemporary(contentsOfAReg) && contentsOfAReg != operand1 && contentsOfAReg != operand2)
   {
	   contentsOfAReg = "";
   }
   if (contentsOfAReg != operand1 && contentsOfAReg != operand2)
   {
	   emit("", "mov", "eax,[" + symbolTable.at(operand2).getInternalName() + "]", "; AReg = " + operand2);
   }
   emit("", "cmp", "eax,[" + symbolTable.at(operand1).getInternalName() + "]", "; compare " + operand2 + " and " + operand1);
   string labelCountFirst = getLabel();
   emit("", "jge", "." + labelCountFirst, "; if " + operand2 + " >= " + operand1 + " then jump to set eax to TRUE");
   emit("", "mov", "eax,[FALSE]", "; else set eax to FALSE");
   // name,SymbolTableEntry(genInternalName(inType),inType,inMode,inValue,inAlloc,inUnits
   symbolTable.insert(pair<string, SymbolTableEntry>("false",SymbolTableEntry("FALSE",BOOLEAN,CONSTANT,whichValue("false"),YES,1)));
   string labelCountSecond = getLabel();
   emit("", "jmp", "." + labelCountSecond, "; unconditionally jump");
   emit("." + labelCountFirst + ":", "", "", "");
   emit("", "mov", "eax,[TRUE]", "; set eax to TRUE");
   symbolTable.insert(pair<string, SymbolTableEntry>("true",SymbolTableEntry("TRUE",BOOLEAN,CONSTANT,whichValue("true"),YES,1)));
   emit("." + labelCountSecond + ":", "", "", "");
   
   // deassign all the temporaries involved and free those names for reuse
   if (isTemporary(operand1))
   {
      freeTemp();
   }
   
   if (isTemporary(operand2))
   {
	   freeTemp();
   }
   
   // get the next available temp and store in the A register
   contentsOfAReg = getTemp();
   symbolTable.at(contentsOfAReg).setDataType(BOOLEAN);
   
   // Push the name of the result onto the stack
   pushOperand(contentsOfAReg);
} // op2 >= op1

// Emit functions for Stage 2
void Compiler::emitThenCode(string operand1, string operand2)
{
   operand1 = operand1.substr(0,15);
	operand2 = operand2.substr(0,15);
   string tempLabel;
	
   if (whichType(operand1) != BOOLEAN)
   {
      processError("if predicate must be of type boolean");
   }
   tempLabel = getLabel();
   
   if (contentsOfAReg != operand1)
   {
	   emit("", "mov", "eax,[" + symbolTable.at(operand1).getInternalName() + "]", "; AReg = " + operand1);
   }
   emit("", "cmp", "eax,0", "; compare eax to 0");
   emit("", "je", "." + tempLabel, "; if " + operand1 + " is false then jump to end of if");
   pushOperand(tempLabel);
   
   if (isTemporary(operand1))
   {
      freeTemp();
   }
   // deassign operands from all registers
   
   contentsOfAReg = "";
   
}
// emit code which follows 'then' and statement predicate
void Compiler::emitElseCode(string operand1, string operand2)
{
   operand1 = operand1.substr(0,15);
	operand2 = operand2.substr(0,15);
   string tempLabel;
   
   tempLabel = getLabel();
   emit("", "jmp", "." + tempLabel, "; jump to end if");
   emit("." + operand1 + ":","","","; else");
   
   pushOperand(tempLabel);
   
   contentsOfAReg = "";
}
// emit code which follows 'else' clause of 'if' statement
void Compiler::emitPostIfCode(string operand1, string operand2)
{
   emit("." + operand1 + ":","","","; end if");
   contentsOfAReg = "";
}
// emit code which follows end of 'if' statement
void Compiler::emitWhileCode(string operand1, string operand2)
{
   operand1 = operand1.substr(0,15);
	operand2 = operand2.substr(0,15);
   string tempLabel;
   
   tempLabel = getLabel();
   emit("." + tempLabel + ":","","","; while");
   pushOperand(tempLabel);
   contentsOfAReg = "";
}
// emit code following 'while'
void Compiler::emitDoCode(string operand1, string operand2)
{
   operand1 = operand1.substr(0,15);
	operand2 = operand2.substr(0,15);
   string tempLabel;
	
   if (whichType(operand1) != BOOLEAN)
   {
      processError("while predicate must be of type boolean");
   }
   tempLabel = getLabel();
   
   if (contentsOfAReg != operand1)
   {
	   emit("", "mov", "eax,[" + symbolTable.at(operand1).getInternalName() + "]", "; AReg = " + operand1);
   }
   emit("", "cmp", "eax,0", "; compare eax to 0");
   emit("", "je", "." + tempLabel, "; if " + operand1 + " is false then jump to end while");
   pushOperand(tempLabel);
   
   if (isTemporary(operand1))
   {
      freeTemp();
   }
   // deassign operands from all registers
   
   contentsOfAReg = "";
   
}
// emit code following 'do'
void Compiler::emitPostWhileCode(string operand1, string operand2)
{
   emit("", "jmp", "." + operand2, "; end while");
   emit("." + operand1 + ":","","","");
   contentsOfAReg = "";
}
// emit code at end of 'while' loop;
// operand2 is the label of the beginning of the loop
// operand1 is the label which should follow the end of the loop
void Compiler::emitRepeatCode(string operand1, string operand2)
{
   operand1 = operand1.substr(0,15);
	operand2 = operand2.substr(0,15);
   string tempLabel = getLabel();
   
   emit("." + tempLabel + ":","","","; repeat");
   pushOperand(tempLabel);
   
   contentsOfAReg = "";
}
// emit code which follows 'repeat'
void Compiler::emitUntilCode(string operand1, string operand2)
{
   operand1 = operand1.substr(0,15);
	operand2 = operand2.substr(0,15);
	
   if (whichType(operand1) != BOOLEAN)
   {
      processError("predicate of until must be of type boolean");
   }
   
   if (contentsOfAReg != operand1)
   {
	   emit("", "mov", "eax,[" + symbolTable.at(operand1).getInternalName() + "]", "; AReg = " + operand1);
   }
   emit("", "cmp", "eax,0", "; compare eax to 0");
   emit("", "je", "." + operand2, "; until " + operand1 + " is true");
   
   if (isTemporary(operand1))
   {
      freeTemp();
   }
   // deassign operands from all registers
   
   contentsOfAReg = "";
   
}
// emit code which follows 'until' and the predicate of loop
// operand1 is the value of the predicate
// operand2 is the label which points to the beginning of the loop

// other routines
void Compiler::freeTemp()
{
   currentTempNo--;
   if (currentTempNo < -1)
   {
      processError("compiler error, currentTempNo should be >= -1");
   }
}
string Compiler::getTemp()
{
   string temp;
   currentTempNo++;
   temp = "T" + to_string(currentTempNo);
   
   if (currentTempNo > maxTempNo)
   {
      insert(temp, UNKNOWN, VARIABLE, "", NO, 1);
      maxTempNo++;
   }
   return temp;
}

string Compiler::getLabel()
{
   string temp;
   static int Lcount = 0;
   

   temp = "L" + to_string(Lcount);
   Lcount++;
   

   
   return temp;
   
}

bool Compiler::isTemporary(string s) const
{
   if (s[0] == 'T')
   {
      return true;
   }
   else
   {
      return false;
   }
} 
// determines if s represents a temporary

// Lexical routines
// next char needs consist of accepted identifiers
char Compiler::nextChar()
{
	sourceFile.get(ch);
   
   static char prevChar = '\n';
   
 
   if (sourceFile.eof())
   {
      ch = END_OF_FILE; //use a special character to designate end of file
   }
   else
   {
      if (prevChar == '\n')
      {
         listingFile << setw(5) << ++lineNo << "|";
      }
      listingFile << ch;
   }
   prevChar = ch;
   return ch;
} 
// returns the next character or END_OF_FILE marker
string Compiler::nextToken()
{
   token = "";
	while (token == "")
	{
		if (ch == '{') 
      { // process comment
      while ((nextChar() != '}') && (ch != END_OF_FILE)) 
         {}
			if (ch == END_OF_FILE) 
			{
				processError("unexpected end of file");
			} 
			else
			{
				nextChar();
			}
		}
		else if (ch == '}') 
		{
			processError("'}' cannot begin token");
		}
		else if (isspace(ch)) 
		{
			nextChar();
		}
		else if (isSpecialSymbol(ch)) 
		{
         token = ch;
			nextChar();
         
         if (token == ":" && ch == '=')
         {
               token += ch;
               nextChar();
         }
         else if (token == "<" && ch == '=')
         {
               token += ch;
               nextChar();
         }
         else if (token == ">" && ch == '=')
         {
               token += ch;
               nextChar();

         }
         else if (token == "<" && ch == '>')
         {

               token += ch;
               nextChar();
         }
		}
		else if (islower(ch)) 
		{
			token = ch;
			while ((islower(nextChar()) || isdigit(ch) || ch == '_') && ch != END_OF_FILE) 
			{
            if (token.back() == '_' && ch == '_')
            {
               processError("\"_\" must be followed by a letter or number");
            }
               token += ch;
			}
			if (ch == END_OF_FILE) 
			{
				processError("unexpected end of file");
			}
		}
		else if (isdigit(ch)) 
		{
			token = ch;
			while (isdigit(nextChar()) && ch != END_OF_FILE)
			{
				token += ch;
			}
			if (ch == END_OF_FILE) 
			{
				processError("unexpected end of file");
			}
		}
		else if (ch == END_OF_FILE) 
		{
			token =  ch;
		}
		else 
		{
			processError("illegal symbol");
		}
	}
	return token;
}
// returns the next token or END_OF_FILE marker
// Other routines
string Compiler::genInternalName(storeTypes stype) const
{
   string conststr;
   
   static int countB, countP, countI;
    
   if (stype == BOOLEAN)
   {
       conststr = "B";
       conststr += to_string(countB);
       countB++;
   }
   if (stype == PROG_NAME){
       conststr = "P";
       conststr += to_string(countP);
       countP++;
   }
   
   if (stype == INTEGER)
   {
       conststr = "I";
       conststr += to_string(countI);
       countI++;
   }


   return conststr;
}  
void Compiler::processError(string err)
{
   errorCount++;
   listingFile << endl << "Error: " << "Line " << lineNo << ": " << err << endl << endl;
   createListingTrailer();
   exit(1);
}