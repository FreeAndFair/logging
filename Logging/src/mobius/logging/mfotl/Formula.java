package mobius.logging.mfotl;

//TODO add specs and docs

/*
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
        new Operator(); // Initializing the Operator
        
        lexer(_formula);
        my_logger.info("Read Formula: " + _formula + ". With Length " + my_formula_parts.length);
        my_temporal_formula = new TemporalFormula(my_formula_parts);
        
        getFreeVar();
        getTemporalSubformula();
    }
        
    /*
     * 
     */
    public boolean evaluation(Structure structure) {
        //@ assert false;
        assert false;
        // TODO bottom implementation
        return true;
    }
    
    /*
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
	    my_logger.info("");
	}
	
	/*
	 * Formulae with no temporal operators is first-order
	 */
	public boolean isFirstOrder(final String[] _parts) {
	    boolean isFO = true;
	    for (int i = 0; i < _parts.length; i++) {
	        if (_parts[i].equals("U") | _parts[i].equals("S") | _parts[i].equals("N") | _parts[i].equals("P")) {
	            isFO = false;
	            break;
	        }
	    }
	    return isFO;
	}
	
	private void lexer(final String _formula_str) {
	    String formula_str = _formula_str;
        
        String formulaWSpace = "";
        String words = "";
        for (int i = 0; i < formula_str.length(); i++) {
            final char character = formula_str.charAt(i);
            
//            System.out.println("------------->>>>>" + formulaWSpace);
            
            if ((character == '(') || (character == ')')
                    || (character == '[') || (character == ',')
                    || (character == '=') || (character == '<')
                    || (character == ' ')
                    || Operator.isFirstOrder(Character.toString(character))
                    || Operator.isTemporal(Character.toString(character))) {
                formulaWSpace += words;
                formulaWSpace += " ";
                
                if (character != ' ') {
                    formulaWSpace += Character.toString(character);
                    formulaWSpace += " ";
                }
                words = "";
            } else {
                words += Character.toString(character);
                if (!words.matches("[a-zA-Z0-9]+")) {
                    my_logger.error("Illegal Letter in Formula!!!");
                }
                
                if (i == (formula_str.length() - 1)) {
                    formulaWSpace += words;
                    formulaWSpace += " ";
                    words = "";
                }
            }
        }
        
        while (formulaWSpace.charAt(0) == ' ') {
            formulaWSpace = formulaWSpace.substring(1);
            
            if (formulaWSpace.length() == 0) {
                my_logger.error("EMPTY FORMULA!!!");
            }
        }
        
        formula_str = formulaWSpace.replaceAll("[ ]+", " ");
        my_logger.info("Formula with Space: " + formula_str);
        my_formula_parts = formula_str.split(" ");
        
        /*
        for (int i = 0; i < formula_parts.length; i++) {
            System.out.println(i + "*" + formula_parts[i]);
        }*/
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
