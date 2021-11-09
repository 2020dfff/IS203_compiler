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
WORD (" ")
KEYWORD ("return"|"break"|"if"|"else"|"continue"|"while"|"aafor"|"fprintf") 
CONST ({DIGIT}+"."{DIGIT}+|{INT}|{DIGIT})
OPT ("|"|"~"|"&"|"-"|"*"|"/"|"+"|"^"|"="|":="|"=="|"!="|">"|"<"|"<="|">="|"!!="|"||"|"&&")
TYPEID (Int)|(Float)|(String)|(Bool)|(Void)
DIGIT [0-9]
func ("main"|"max")
INT {DIGIT}+
OBJECTED [a-z]
Comment ("#").*
Com ("func")
Bracket ("("|")"|"{"|"}"|"["|"]"|";")
Next ("\n") 
%%
{WORD} {
	words++;
	chars+=yyleng;
}
{KEYWORD} {
	chars+=yyleng;
	AddOutput(Row, "KEYWORD", yytext);
} 
{OPT} {
	chars+=yyleng;
	print(Row,yytext);
} 
{OBJECTED} {
	++chars;
    AddOutput(Row, "OBJECTED", yytext);
}
{func} {
	chars+=yyleng;
    AddOutput(Row,"func", yytext);
}
{TYPEID} {
	chars+=yyleng;
	AddOutput(Row, "TYPEID", yytext);
} 
{CONST} {
	chars+=yyleng;
	AddOutput(Row, "CONST", yytext);
} 
{Bracket} {
	chars+=yyleng;
    print(Row,yytext);
} 
{Comment} {chars+=yyleng;} 
{Com} {chars+=yyleng;} 
{Next} {++Row;chars++;} 
.      {chars++;}
%%
int yywrap()
{
	printf("%s", Ans);
    printf("lines:%d,words:%d,chars:%d\n",Row, words, chars);
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

