package demtech.mfotl;

import java.util.regex.Pattern;

/**
 * <p>
 * Class <code>MFOTLFormula</code> is the main component in the mfotl package.
 * It takes a formula of type string, and processes it into a <code>TemporalFormula</code>,
 * which has a linked list type.
 * </p>
 */
public class MFOTLFormula {
    // Attributes
    private final TemporalFormula my_formula;

    private String[] my_tokens;
    private final Pattern my_token_pattern = Pattern.compile("([a-zA-Z]\\w*)|(\\d*)");
    private final Logger my_logger = new Logger(false);
    
    // Constructors
    //@ assignable my_signature;
    //@ assignable my_formula_str;
    //@ ensures my_formula_str == a_formula;
    public MFOTLFormula(final String my_formula_str, final Signature a_signature) {
        super();
        my_logger.debug("Initialize: MFOTLFormula(String)");

        runLexer(my_formula_str);
        
        my_formula = new TemporalFormula(my_tokens, a_signature);
        my_formula.init();
    }
    
    //@ pure
    public boolean evaluateTruth(final Structure a_structure) {
        my_logger.debug("InMethod: MFOTLFormula.evaluate");
        
        return my_formula.evaluateTruth(a_structure);
    }
    
    //@ assignable my_token;
	private void runLexer(final String my_formula_str) {
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

    //@ pure
	public TemporalFormula getFormula() {
	    return this.my_formula;
	}
	
	//@ pure
	public String toString() {
	    return this.my_formula.toString();
	}
}
