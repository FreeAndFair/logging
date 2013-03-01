package mobius.logging.mfotl;

import java.util.HashSet;
import java.util.Set;

//TODO add specs and docs

/**
 * <p>
 * Class <code>MFOTLFormula</code> is the main component in the mfotl package.
 * It takes a fromula of type string, and processes it into a <code>TemporalFormula</code>,
 * which has a linked list type.
 * </p>
 */
public class MFOTLFormula implements Cloneable{
    // Attributes
    public TemporalFormula my_formula;
    public Set<TemporalFormula> my_temporal_subformula;
    private String[] my_formula_parts;    
    private final Logger my_logger = new Logger();
    
    // Constructors
    public MFOTLFormula(final String a_formula) {
        my_logger.debug("Initialize: MFOTLFormula(String)");

        /**
         * check lexer
         */
        lexer(a_formula);
        my_logger.info("Read Formula: " + a_formula + ". With Length " + my_formula_parts.length);
        /**
         * main formula
         */
        my_formula = new TemporalFormula(my_formula_parts);
        
        /**
         * get temporal subformula
         */
        my_temporal_subformula = new HashSet<TemporalFormula>();
        getTemporalSubformula(my_formula);
        
        /**
         * print info
         */
        my_logger.info("\nThe MFOTL formula: " + my_formula.toString());
        my_logger.info("\nThe MFOTL temporal sub formula: ");
        for (Formula i: my_temporal_subformula) {
            my_logger.info(i.toString());
        }
    }
        
    /**
     * 
     */
    public boolean evaluation(final Structure a_structure) {
        /**
         * @ assert false;
         * assert false;
         */

        return my_formula.evaluate(a_structure);
    }
    

    /**
     * <p>
     * <code>getTemporalSubformula</code> Get the temporal subformula
     * </p>
     */
    private void getTemporalSubformula(final Formula a_formula) {
        final Formula temp_formula = a_formula;
        
        if (temp_formula == null) {
            return;
        }
        
        if (temp_formula.my_is_temporal) {
            my_temporal_subformula.add((TemporalFormula) temp_formula);
        } else if (temp_formula instanceof TemporalFormula) {
                getTemporalSubformula(((TemporalFormula) temp_formula).my_left_subformula);
                getTemporalSubformula(((TemporalFormula) temp_formula).my_right_subformula);
        }
    }
    
    /**
     * <p>
     * <code>lexer</code> processes the input formula string, and splits it input an array of String
     * </p>
     */
	private void lexer(final String a_formula_str) {
	    String formula_str = a_formula_str;
        String formula_with_space = "";
        String temp_word = "";
        
        for (int i = 0; i < formula_str.length(); i++) {
            final String temp_str = Character.toString(formula_str.charAt(i));
            
            if (ReservedSymbol.isReserved(temp_word) || ReservedSymbol.isReserved(temp_str)) {
                /*
                final Pattern pattern = Pattern.compile("[^a-zA-Z]+[a-zA-Z0-9]* | [^0-9]+");
                if (!pattern.matcher(temp_word).find() && !ReservedSymbol.isReserved(temp_word)) {
                    my_logger.error("lexer error: " + temp_word);
                }
                */
                formula_with_space = formula_with_space.concat(temp_word).concat(" ");
                if (" ".equals(temp_str)) {
                    temp_word = "";
                } else {
                    temp_word = temp_str;
                }
            } else {
                temp_word = temp_word.concat(temp_str);
            }
        }
        formula_with_space = formula_with_space.concat(temp_word);
        
        
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

    public Object clone() throws CloneNotSupportedException {
        return super.clone();
    }
	
	/*
	 * TODO implement Syntactic sugar
	 */
}
