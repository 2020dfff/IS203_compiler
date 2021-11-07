%option main
%option yywrap
%{
    #include <stdio.h>
    #include <string.h> 
	int Row=0;
    int chars=0;
    int words=0;
	char *Ans = "";
%}
KEYWORD ("return"|"break"|"if"|"else"|"continue"|"while"|"aafor"|"fprintf") 
OPT ("|"|"~"|"&"|"-"|"*"|"/"|"+"|"^"|"="|":="|"=="|"!="|">"|"<"|"<="|">="|"!!="|"||"|"&&")
TYPEID (Int)|(Float)|(String)|(Bool)|(Void)
DIGIT [0-9]
func ("main"|"max")
INT {DIGIT}+
OBJECTED [a-z]
FLOAT {DIGIT}+"."{DIGIT}+
LETTER [a-zA-Z] 
Comment ("#").*
Com ("func")
Type ("int"|"double"|"short"|"char"|"void"|"long")
Bracket ("("|")"|"{"|"}"|"["|"]"|";")
CONST ({INT}|{DIGIT})
Next ("\n") 
WORD ("111111")
%%
{Type} {
	AddOutput(Row, "type", yytext);
}  
{KEYWORD} {
	AddOutput(Row, "KEYWORD", yytext);
} 
{OPT} {
	print(Row,yytext);
} 
{OBJECTED} {
    AddOutput(Row, "OBJECTED", yytext);
}
{func} {
    AddOutput(Row,"func", yytext);
}
{TYPEID} {
	AddOutput(Row, "TYPEID", yytext);
} 
{CONST} {
	AddOutput(Row, "CONST", yytext);
} 
{Bracket} {
    print(Row,yytext);
} 
{Comment} {} 
{Com} {} 
{Next} {++Row;chars++;} 
.      {chars++;}
{WORD} {words++; chars += yyleng;}
%%
int yywrap()
{
	printf("%s", Ans);
    printf("lines:%d,words:%d,chars:%d",Row,words,chars);
	return 1;
} 
void AddOutput(int Row, char* type, char* text){ 
	char str[50];
	sprintf(str, "#%d %s %s\n", Row, type, text);
	char *tmp = Ans; 
	Ans = (char *) malloc(strlen(tmp) + strlen(str) + 1);
	sprintf(Ans, "%s%s", tmp, str); 
	if(strlen(tmp) > 0)
		free(tmp);
	return ;
}

void print(int Row,char* text)
{
    char str[50];
	sprintf(str, "#%d %s\n", Row, text);
	char *tmp = Ans; 
	Ans = (char *) malloc(strlen(tmp) + strlen(str) + 1);
	sprintf(Ans, "%s%s", tmp, str); 
	if(strlen(tmp) > 0)
		free(tmp);
	return ; 
}

