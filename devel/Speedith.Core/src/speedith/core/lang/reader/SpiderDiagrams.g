grammar SpiderDiagrams;

options {
	output=AST;
	ASTLabelType=CommonTree;
}

/* These tokens are used simply as indicator 'head' nodes in the generated AST
tree. */
tokens {
	DICT       =         '{';	// The 'dictionary' node in the generated AST (contains KEY_VALUE nodes).
	PAIR       =         '=';		// The 'key value' node in the AST.
	LIST       =         '[';		// The 'list' node (contains comma separated elements enclosed in block braces '[' and ']').
	SLIST      =         '(';		// The 'sorted list' node (contains comma separated elements enclosed in parentheses '(' and ')').
	SD_PRIMARY = 'PrimarySD';	// The 'primary spider diagram'.
	SD_BINARY  =  'BinarySD';	// The 'binar spider diagram'.
	SD_UNARY   =   'UnarySD';	// The 'unary spider diagram'.
	SD_NULL    =    'NullSD';	// The 'null spider diagram'.
}

@parser::header {
package speedith.core.lang.reader;
import static speedith.core.i18n.Translations.i18n;
}

@lexer::header {
package speedith.core.lang.reader;
import static speedith.core.i18n.Translations.i18n;
}

@rulecatch {
catch (RecognitionException e) {
    throw new ParseException(i18n("ERR_PARSE_INVALID_SYNTAX"), e, this);
}
}

@lexer::rulecatch {
catch (RecognitionException e) {
    throw new ParseException(i18n("ERR_PARSE_INVALID_SYNTAX"), e, this);
}
}

@members {
@Override
public void reportError(RecognitionException e) {
    throw new ParseException(i18n("ERR_PARSE_INVALID_SYNTAX"), e, this);
}
}

@lexer::members {
@Override
public void reportError(RecognitionException e) {
    throw new ParseException(i18n("ERR_PARSE_INVALID_SYNTAX"), e, this);
}
}




/*******************************************************************************
								  Parser section
*******************************************************************************/


/* Entry. */
start
	:	spiderDiagram
	;

spiderDiagram
	:	'PrimarySD'^ '{'! (keyValue (','! keyValue)*)? '}'!
	|	'UnarySD'^ '{'! (keyValue (','! keyValue)*)? '}'!
	|	'BinarySD'^ '{'! (keyValue (','! keyValue)*)? '}'!
	|	'NullSD'^ ('{'! (keyValue (','! keyValue)*)? '}'!)?
	;

keyValues
	:	'{'^ (keyValue (','! keyValue)*)? '}'!
	;

list
	:	'['^ (languageElement (','! languageElement)*)? ']'!
	;
	
sortedList
	:	'('^ (languageElement (','! languageElement)*)? ')'!
	;

keyValue
	:	ID '='^ languageElement
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