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
COMMENT ^#[^\n]*
TYPE (INT)|(FLOAT)|(String)|(Bool)|(Void)

%%
\n      {++num_lines; ++num_chars;}
.       {++num_chars;}
{DIGIT} {nDigitNumber=nDigitNumber+1;}
%%

int main()
{
    yylex();
    fprintf(stderr,"\nNumber of digit=%d\n",nDigitNumber);
    return(0);
}