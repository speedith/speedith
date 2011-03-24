grammar SpiderDiagrams;




/*******************************************************************************
								  Parser section
*******************************************************************************/


/* Entry. */
spiderDiagram
	:	unitarySD
	|	compoundSD
	|	'NullSD'
	;

unitarySD
	:	'UnitarySD' habitats shadedZones
	;

compoundSD
	:	ID unitarySD unitarySD
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