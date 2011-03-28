tree grammar SpiderDiagramsTG;

options {
	tokenVocab=SpiderDiagrams;
	ASTLabelType=CommonTree;
	filter=true;
}

@header {
package speedith.lang.parser;
}


spiderDiagram
	:	^(SD_PRIMARY keyValue*)
	|	^(SD_UNARY keyValue*)
	|	^(SD_BINARY keyValue*)
	|	^(SD_NULL keyValue*)
	;

keyValues
	:	^(DICT keyValue*)
	;

list
	:	^(LIST languageElement*)
	;
	
sortedList
	:	^(SLIST languageElement*)
	;

keyValue
	:	^(PAIR ID languageElement)
	;

languageElement
	:	STRING
	;