//匹配到换行符时，字符数+1，行数+1
//匹配到其它任何字符，只增加字符数
//匹配到单词(没有空白符的连续串)时，单词数+1，字符数+=单词长度

1. 行数从第0行开始数。
2. 不用输出逗号。



目标：
利用flex编写一个词法分析器，能够:
1.提取出.sealpp文件中的各种单词
2.排除注释
3.正确标定单词行号
4.计算整个.sealpp文件中的行数，字数，字符数。


单词包括：

关键词"fprintf","while","aafor","if","else","continue","break","return"
运算符（+ - * / % &&  & < <= > >=等）
常量（整型、浮点、字符串、布尔）
符号（函数名、变量名）
其他符号（逗号、分号、括号等）




