grammar SpiderDiagrams;

options {
	output=AST;
	ASTLabelType=CommonTree;
}

/* These tokens are used simply as indicator 'head' nodes in the generated AST
tree. */
tokens {
	DICT;		// The 'dictionary' node in the generated AST (contains KEY_VALUE nodes).
	PAIR;		// The 'key value' node in the AST.
	LIST;		// The 'list' node (contains comma separated elements enclosed in block braces '[' and ']').
	SLIST;		// The 'sorted list' node (contains comma separated elements enclosed in parentheses '(' and ')').
	SD_PRIMARY;	// The 'primary spider diagram'.
	SD_BINARY;	// The 'binar spider diagram'.
	SD_UNARY;	// The 'unary spider diagram'.
	SD_NULL;	// The 'null spider diagram'.
}

@parser::header {
package speedith.core.lang.parser;
}

@lexer::header {
package speedith.core.lang.parser;
}




/*******************************************************************************
								  Parser section
*******************************************************************************/


/* Entry. */
start
	:	spiderDiagram
	;

spiderDiagram
	:	'PrimarySD' '{' (keyValue (',' keyValue)*)? '}'
		->	^(SD_PRIMARY keyValue*)
	|	'UnarySD' '{' (keyValue (',' keyValue)*)? '}'
		->	^(SD_UNARY keyValue*)
	|	'BinarySD' '{' (keyValue (',' keyValue)*)? '}'
		->	^(SD_BINARY keyValue*)
	|	'NullSD' '{' (keyValue (',' keyValue)*)? '}'
		->	^(SD_NULL keyValue*)
	;

keyValues
	:	'{' (keyValue (',' keyValue)*)? '}'
		->	 ^(DICT keyValue*)
	;

list
	:	'[' (languageElement (',' languageElement)*)? ']'
		->	^(LIST languageElement*)
	;
	
sortedList
	:	'(' (languageElement (',' languageElement)*)? ')'
		->	^(SLIST languageElement*)
	;

keyValue
	:	ID '=' languageElement
		->	^(PAIR ID languageElement)
	;

languageElement
	:	STRING
	|	keyValues
	|	list
	|	sortedList
	|	spiderDiagram
	;



/*******************************************************************************
								  Lexer section
*******************************************************************************/

COMMENT
    :   '//' ~('\n'|'\r')* '\r'? '\n' {$channel=HIDDEN;}
    |   '/*' ( options {greedy=false;} : . )* '*/' {$channel=HIDDEN;}
    ;

WS  :   ( ' '
        | '\t'
        | '\r'
        | '\n'
        ) {$channel=HIDDEN;}
    ;

STRING
	:	'"' ( ESC_SEQ | ~('\\'|'"') )* '"'
	;

fragment
HEX_DIGIT
	:	('0'..'9'|'a'..'f'|'A'..'F')
	;

fragment
ESC_SEQ
	:	'\\' ('b'|'t'|'n'|'f'|'r'|'\"'|'\''|'\\')
	|	UNICODE_ESC
	|	OCTAL_ESC
	;

fragment
OCTAL_ESC
	:	'\\' ('0'..'3') ('0'..'7') ('0'..'7')
	|	'\\' ('0'..'7') ('0'..'7')
	|	'\\' ('0'..'7')
	;

fragment
UNICODE_ESC
	:	'\\' 'u' HEX_DIGIT HEX_DIGIT HEX_DIGIT HEX_DIGIT
	;

ID
	:	IdentifierStart IdentifierPart*
	;

fragment
IdentifierStart
	:	'\u0024'
	|	'\u0041'..'\u005a'
	|	'\u005f'
	|	'\u0061'..'\u007a'
	|	'\u00a2'..'\u00a5'
	|	'\u00aa'
	|	'\u00b5'
	|	'\u00ba'
	|	'\u00c0'..'\u00d6'
	|	'\u00d8'..'\udfff'
	;					 
							  
fragment 
IdentifierPart
	:	'\u0000'..'\u0008'
	|	'\u000e'..'\u001b'
	|	'\u0024'
	|	'\u0030'..'\u0039'
	|	'\u0041'..'\u005a'
	|	'\u005f'
	|	'\u0061'..'\u007a'
	|	'\u007f'..'\u009f'
	|	'\u00a2'..'\u00a5'
	|	'\u00aa'
	|	'\u00ad'
	|	'\u00b5'
	|	'\u00ba'
	|	'\u00c0'..'\u00d6'
	|	'\u00d8'..'\udfff'
	;