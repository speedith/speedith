package spiderdrawer.shape;

public enum Logical {
    EQUIVALENCE, IMPLICATION, DISJUNCTION, CONJUNCTION, NEGATION;
    
    
    public static Logical create(int type) {
    	switch (type) {
			case 0: return EQUIVALENCE;
			case 1: return IMPLICATION;
			case 2: return DISJUNCTION;
			case 3: return CONJUNCTION;
			case 4: return NEGATION;
			default: return null;
    	}
    }
    
    public static Logical create(char character) {
    	switch (character) {
			case '\u2194': return EQUIVALENCE;
			case '\u2192': return IMPLICATION;
			case '\u2228': return DISJUNCTION;
			case '\u2227': return CONJUNCTION;
			case '\u00AC': return NEGATION;
			default: return null;
    	}
    }
}