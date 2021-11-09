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
Next [\n]
DELIM [\t ]
WORD {DELIM}+
NEWLINE ^\n
BLANK ^[ \t]+
DIGIT [0-9]
LETTER [a-zA-Z]
COMNAME ({DIGIT}+"."{LETTER}+)
COMCONTENT .*
TITLECOMMENT ("# "{COMNAME})
COMMENT ("#").*
COMFUNC ("func "{OBJECTED})
PLAHOLD ("%f"|"%s"|"%lld")
stderr ("stderr")
OBJECTED [a-z]({LETTER}|_|{DIGIT})*
OPT ("|"|"~"|"&"|"-"|"*"|"/"|"+"|"^"|"="|":="|"%"|"=="|"!="|">"|"<"|"<="|">="|"!!="|"||"|"&&")
Bracket ("("|")"|"{"|"}"|"["|"]"|";")
KEYWORD ("return"|"break"|"if"|"else"|"continue"|"while"|"aafor"|"fprintf") 
INT {DIGIT}+
FLOAT {DIGIT}+"."{DIGIT}+
CONST ({FLOAT}|{INT}|{DIGIT})
TYPEID (Int)|(Float)|(String)|(Bool)|(Void)
%%
{KEYWORD} {
	chars+=yyleng;
	AddOutput(Row, "KEYWORD", yytext);
} 
{OPT} {
	chars+=yyleng;
	print(Row,yytext);
} 
{PLAHOLD} {
	chars+=yyleng;
	print(Row,yytext);
} 
{stderr} {chars+=yyleng;}
{OBJECTED} {
	++chars;
    AddOutput(Row, "OBJECTED", yytext);
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
{NEWLINE} {Row++;chars++;}
{BLANK} {chars+=yyleng;}
{TITLECOMMENT} {
	chars+=yyleng;
	yyless(2);
	words++;
} 
{COMNAME} {titleprint(yytext);}
{COMMENT} {
	chars+=yyleng;
}
{COMFUNC} {
	chars+=yyleng;words++;
	print(Row,yytext);
} 
{Next} {++Row;chars++;words++;} 
{WORD} {
	words++;
	chars+=yyleng;
}
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
void titleprint(char* text)
{
	char str[50];
	sprintf(str, "#name %s\n", text);
	char *tmp = Ans; 
	Ans = (char *) malloc(strlen(tmp) + strlen(str) + 1);
	sprintf(Ans, "%s%s", tmp, str); 
	if(strlen(tmp) > 0)
		free(tmp);
	return ; 
}

