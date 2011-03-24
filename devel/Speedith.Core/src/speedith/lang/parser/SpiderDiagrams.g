grammar SpiderDiagrams;

@header {
package speedith.lang.parser;
}

@lexer::header {
package speedith.lang.parser;
}




/*******************************************************************************
								  Parser section
*******************************************************************************/


/* Entry. */
spiderDiagram
	:	unitarySD
	|	compoundSD
	|	nullSD
	;

nullSD
	:	'NullSD' (attributes)?
	;

unitarySD
	:	'UnitarySD' habitats shadedZones (attributes)? (spiderNames)?
	;

attributes
	:	'Attributes' keyValues
	;

keyValues
	:	'{' (keyValue (',' keyValue)*)? '}'
	;

keyValue
	:	ID '=' STRING
	;

spiderNames
	:	'SpiderNames' stringList
	;

stringList
	:	'[' (STRING (',' STRING)*)? ']'
	;

compoundSD
	:	ID unitarySD unitarySD (attributes)?
	;

shadedZones
	:	'{' (zone (',' zone)*)? '}'
	;

region
	:	'{' (zone (',' zone)*)? '}'
	;

zone
	:	'(' setSet ',' setSet ')'
	;

setSet
	:	'{' (ID (',' ID)*)? '}'
	;

habitats
	:	'[' (region (',' region)*)? ']'
	;




/*******************************************************************************
								  Lexer section
*******************************************************************************/

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