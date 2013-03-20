package mobius.logging.mfotl;

import java.util.HashSet;
import java.util.Set;
import java.util.regex.Pattern;

//TODO add specs and docs

/**
 * <p>
 * Class <code>MFOTLFormula</code> is the main component in the mfotl package.
 * It takes a formula of type string, and processes it into a <code>TemporalFormula</code>,
 * which has a linked list type.
 * </p>
 */
public class MFOTLFormula {
    // Attributes
    public TemporalFormula my_formula;
    public final String my_formula_str;
    public final Signature my_signature;

    private String[] my_tokens;
    private final Set<TemporalFormula> my_temporal_subformula;
    private final Pattern my_token_pattern = Pattern.compile("([a-zA-Z]\\w*)|(\\d*)");
    private final Logger my_logger = new Logger(true);
    
    // Constructors
    //@ ensures my_formula_str == a_formula
    public MFOTLFormula(final /*@ non_null @*/ String a_formula, final /*@ non_null @*/ Signature a_signature) {
        my_logger.debug("Initialize: MFOTLFormula(String)");
        
        my_signature = a_signature;
        my_formula_str = a_formula;
        /**
         * lexical analysis and formula building
         */
        runLexer();
        
        my_formula = new TemporalFormula(my_tokens, my_signature);
        my_temporal_subformula = new HashSet<TemporalFormula>();
    }
    
    public MFOTLFormula(final /*@ non_null @*/ MFOTLFormula a_MFOTLFormula, final /*@ non_null @*/ Signature a_signature) {
        this(a_MFOTLFormula.my_formula_str, a_signature);
    }
        
    /**
     * <p>
     * <code>evaluate</code> a MFOTL formula
     * </p> 
     */
    //@ pure
    public boolean evaluate(final Structure a_structure) {
        my_logger.debug("InMethod: MFOTLFormula.evaluate");
        
        if (a_structure == null)
            return false;
        
        return (my_formula.evaluate(a_structure).size() != 0);
    }
    
    public Set<TemporalFormula> getTemporalSubformula() {
        /**
         * get temporal sub-formula
         */
        getTemporalSubformula(my_formula);
        
        /**
         * print info
         */
        my_logger.info("\nThe MFOTL formula: " + my_formula.toString());
        my_logger.debug("\nThe MFOTL temporal sub formula: ");
        for (Formula i: my_temporal_subformula) {
            my_logger.debug(i.toString());
        }
        
        return my_temporal_subformula;
    }

    
    /**
     * <p>
     * <code>getTemporalSubformula</code> Get the temporal subformula
     * </p>
     */
    //@ pure
    private void getTemporalSubformula(final /*@ non-null */ Formula a_formula) {
        if (a_formula.my_is_temporal) {
            my_temporal_subformula.add((TemporalFormula) a_formula);
        } else if (a_formula instanceof TemporalFormula) {
                getTemporalSubformula(((TemporalFormula) a_formula).my_left_subformula);
                getTemporalSubformula(((TemporalFormula) a_formula).my_right_subformula);
        }
    }
    
    /**
     * <p>
     * <code>lexer</code> processes the input formula string, and splits it input an array of String
     * </p>
     */
    //@ assignable my_token
	private void runLexer() {
	    String temp_formula_str = my_formula_str;
        String temp_formula_with_space = "";
        String temp_token = "";
        
        for (int i = 0; i < temp_formula_str.length(); i++) {
            final String temp_str = Character.toString(temp_formula_str.charAt(i));
            
            if (ReservedSymbol.isReserved(temp_token) || ReservedSymbol.isReserved(temp_str)) {
                if (!ReservedSymbol.isReserved(temp_token)
                        && !my_token_pattern.matcher(temp_token).find()) {
                    my_logger.error("lexer error: " + temp_token);
                }
                
                temp_formula_with_space = temp_formula_with_space.concat(temp_token).concat(" ");
                if (" ".equals(temp_str)) {
                    temp_token = "";
                } else {
                    temp_token = temp_str;
                }
            } else {
                temp_token = temp_token.concat(temp_str);
            }
        }
        
        temp_formula_with_space = temp_formula_with_space.concat(temp_token);
        
        while (temp_formula_with_space.charAt(0) == ' ') {
            temp_formula_with_space = temp_formula_with_space.substring(1);
            
            if (temp_formula_with_space.length() == 0) {
                my_logger.error("EMPTY FORMULA!!!");
            }
        }
        
        temp_formula_str = temp_formula_with_space.replaceAll("[ ]+", " ");
        my_logger.info("Formula with Space: " + temp_formula_str);
        my_tokens = temp_formula_str.split(" ");
        
        my_logger.info("Read formula: " + my_formula_str + ", with " + my_tokens.length + " tokens");
	}
/*
    protected Object clone() throws CloneNotSupportedException {
        MFOTLFormula new_MFOTLFormula = (MFOTLFormula) super.clone();
        new_MFOTLFormula.my_formula = (TemporalFormula) this.my_formula.clone();
        return new_MFOTLFormula;
    }
	*/
	/*
	 * TODO implement removing syntactic sugar
	 */
}
