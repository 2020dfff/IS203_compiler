%{
#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
int lines=0;
int words=0;
int chars=0;
%}

DIGIT [0-9]
INT {DIGIT}+
FLOAT {DIGIT}+"."{DIGIT}+
CONST ({INT}|{DIGIT})
COMMENT ^#[^\n]*
TYPEID (INT)|(FLOAT)|(String)|(Bool)|(Void)
DELIM [\t  " "]
WS {DELIM}+
NEWLINE [\n]+
OBJECT [a-z]({LETTER}|_|DIGIT)*
OPT ("|"|"~"|"&"|"-"|"*"|"/"|"+"|"^"|"="|":="|"=="|"!="|">"|"<"|"<="|">="|"!!="|"||"|"&&")
BRACKET (";"|"{"|"}"|"("|")")
PLAHOLD ("%f"|"%s"|"%lld")
KEYWORD ("return"|"break"|"if"|"else"|"continue"|"while"|"aafor"|"fprintf") 
WORD ([^ \t\n\r\a]+)
%%

\n      {lines++; chars++;}
.       {chars++;}
{WORD}		{ words++; chars += yyleng; return 1;}
<<EOF>>		{ return 0;}

%%

int main()
{
   yylex();
	fprintf("#%s\t%d", lines, yytext);
    fprintf("lines:%d\twords:%d\tchars:%d\n", chars, words, lines);
}
