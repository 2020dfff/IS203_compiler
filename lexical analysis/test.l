%option main
%option yywrap
%{
    #include <stdio.h>
    #include <string.h> 
	int Row=0;
	char *Ans = "";
%}
KEYWORD ("return"|"break"|"if"|"else"|"continue"|"while"|"aafor"|"fprintf") 
OPT ("|"|"~"|"&"|"-"|"*"|"/"|"+"|"^"|"="|":="|"=="|"!="|">"|"<"|"<="|">="|"!!="|"||"|"&&")
TYPEID (Int)|(Float)|(String)|(Bool)|(Void)
DIGIT [0-9]
func ("main")
INT {DIGIT}+
Decimal {INT}.{DIGIT}+
OBJECT [a-z]({LETTER}|_|{DIGIT})*
FLOAT {DIGIT}+"."{DIGIT}+
LETTER [a-zA-Z] 
Comment ("#").* 
Type ("int"|"double"|"short"|"char"|"void"|"long")
Bracket ("("|")"|"{"|"}"|"["|"]"|";")
CONST ({INT}|{DIGIT})
Next ("\n") 
%%
{Type} {
	AddOutput(Row, "type", yytext);
}  
{KEYWORD} {
	AddOutput(Row, "KEYWORD", yytext);
} 
{OPT} {
	AddOutput(Row, "", yytext);
} 
{OBJECT} {
    AddOutput(Row, "OBJECT", yytext);
}
{func} {
    AddOutput(Row,"func", yytext);
}
{TYPEID} {
	AddOutput(Row, "TYPEID", yytext);
} 
{INT} {
	AddOutput(Row, "INT", yytext);
} 
{Decimal} {
	AddOutput(Row, "decimal", yytext);
} 
{FLOAT} { 
	char *p = strchr(yytext, 'e');
	if (p && yytext[strlen(yytext)-1] == 'e'){
		printf("Error at Line %d: Illegal floating point number \"%s\".\n",Row,yytext);
		return;
	} else {
		AddOutput(Row, "FLOAT", yytext);
	}
} 
{Next} {++Row;} 
  
{Bracket} {
	AddOutput(Row, "", yytext);
} 
 
{Comment} {} 
. {}
%%
int yywrap()
{
	printf("%s", Ans);
	return 1;
} 
void AddOutput(int Row, char* type, char* text){ 
	char str[50];
	sprintf(str, "#%d %s\t%s\n", Row, type, text);
	char *tmp = Ans; 
	Ans = (char *) malloc(strlen(tmp) + strlen(str) + 1);
	sprintf(Ans, "%s%s", tmp, str); 
	if(strlen(tmp) > 0)
		free(tmp);
	return ;
}

