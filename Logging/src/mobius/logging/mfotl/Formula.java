package mobius.logging.mfotl;

//TODO add specs and docs

/**
 * 
 */
public class Formula {
    protected String[] my_formula_parts;

    protected String[] my_free_variable;
    
    public TemporalFormula my_temporal_formula;
    public TemporalFormula[] my_temporal_subformula;
    
    public Structure my_structure;
    private final Logger my_logger = new Logger();
    
    public Formula(final String _formula) {
        // initialize Operator
        new Operator();

        lexer(_formula);
        my_logger.info("Read Formula: " + _formula + ". With Length " + my_formula_parts.length);
        my_temporal_formula = new TemporalFormula(my_formula_parts);
        
        getFreeVar();
        
        getTemporalSubformula();
    }
        
    /**
     * 
     */
    public boolean evaluation(final Structure a_structure) {
        //@ assert false;
        assert false;
        // TODO bottom implementation
        return true;
    }
    
    /**
     * <p>
     * Get the temporal subformula
     * </p>
     */
    private void getTemporalSubformula() {
        my_temporal_subformula = new TemporalFormula[5];
        // TODO implement it
        my_logger.info("");
    }
	
	private void getFreeVar() {
	    my_logger.debug("InMethod: getFreeVar");
	}
	
	/*
	 * Formulae with no temporal operators is first-order
	 */
	public boolean isFirstOrder(final String[] _parts) {
	    boolean isFO = true;
	    for (int i = 0; i < _parts.length; i++) {
	        if (Operator.isTemporal(_parts[i])) {
	            isFO = false;
	            break;
	        }
	    }
	    return isFO;
	}
	
	private void lexer(final String a_formula_str) {
	    String formula_str = a_formula_str;
        
        String formula_with_space = "";
        String words = "";
        for (int i = 0; i < formula_str.length(); i++) {
            final char character = formula_str.charAt(i);
            
            if (isResveredSymbol(character) || Operator.isOperator(Character.toString(character))) {
                formula_with_space = formula_with_space.concat(words);
                formula_with_space = formula_with_space.concat(" ");
                
                if (character != ' ') {
                    formula_with_space += Character.toString(character);
                    formula_with_space += " ";
                }
                words = "";
            } else {
                words += Character.toString(character);
                if (!words.matches("[a-zA-Z0-9]+")) {
                    my_logger.error("Illegal Letter in Formula!!!");
                }
                
                if (i == (formula_str.length() - 1)) {
                    formula_with_space += words;
                    formula_with_space += " ";
                    words = "";
                }
            }
        }
        
        while (formula_with_space.charAt(0) == ' ') {
            formula_with_space = formula_with_space.substring(1);
            
            if (formula_with_space.length() == 0) {
                my_logger.error("EMPTY FORMULA!!!");
            }
        }
        
        formula_str = formula_with_space.replaceAll("[ ]+", " ");
        my_logger.info("Formula with Space: " + formula_str);
        my_formula_parts = formula_str.split(" ");
	}
	
	private boolean isResveredSymbol(final char a_symbol) {
	    return ((a_symbol == '(') || (a_symbol == ')')
                || (a_symbol == '[') || (a_symbol == ',')
                || (a_symbol == '=') || (a_symbol == '<')
                || (a_symbol == ' '));
	}
	
	/*
	void removeSyntacticsugar(String[] _part1, String[] _part2, String _op) {
	    if (_op == Operator.op.get(_op))
	        ;
	    else if (_op == Operator.op.get(_op))
	        ;
	    else
	        ;
	}
	*/
}
