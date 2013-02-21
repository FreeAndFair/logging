package mobius.logging.mfotl;

import java.util.HashSet;
import java.util.Set;

//TODO add specs and docs


/**
 * Temporal Formula
 */
public class TemporalFormula extends Formula{
    /*
     * TemporalFormula ::= AtomicFormula
     * TemporalFormula ::= TemporalFormula + Operator + TemporalFormula
     */
    public Formula my_left_subformula = null;
    public Formula my_right_subformula = null;
    
    /*
    public Formula my_atomic_left = null;
    public Formula my_atomic_right = null;
    */
    /**
     * 
     */
    public Operator my_main_operator = null;
    //public TemporalOperator my_temporal_operator = null;
    
    /**
     * check is this temporal formula is first order or not.
     */
    /*
    public boolean is_temporal = false;
    public boolean is_firstorder = true;
    */
    public boolean my_is_true = false;
    
    public static Set my_bound_variable = new HashSet();
    public static Set<String> my_variable = new HashSet();
    // TODO add collection of variables;
    
    private final Logger my_logger = new Logger();
    
    private String[] my_parts;

    public TemporalFormula(final String[] _parts) {
        my_parts = new String[_parts.length];
        System.arraycopy(_parts, 0, my_parts, 0, my_parts.length);
        
        if (my_parts.length == 0) {
            my_logger.info("Temporal Formula with length 0");
        } else {
            parseFormula();
        }
    }
    
    private void removeOuterParenthesis() {
        final String[] tmpparts = new String[my_parts.length-2];
        
        my_logger.info("\nRemove outer most parenthesis");        
        if (my_parts[0].equals("(") && my_parts[my_parts.length-1].equals(")")) {
            System.arraycopy(my_parts, 1, tmpparts, 0, tmpparts.length);
        } else {
            my_logger.error("Remove outer most parenthesis ERROR!!!");
        }
        
        my_parts = tmpparts;
    }

    /**
     * 
     */
    private final void parseFormula() {
        my_logger.debug("InMethod: parseFormula");
        
        int mop = findMainOp();
        
        while ((mop == -2) && (my_parts[0].equals("("))) {
            removeOuterParenthesis();
            mop = findMainOp();
        }
        
        if (mop == -2) {
            my_right_subformula = new AtomicFormula(my_parts);

            my_logger.debug(my_right_subformula.toString() + " -> ATOMIC FORMULA");
            return;
        }
        
        // non atomic formula
        int mop2;
        if (ReservedSymbol.isTemporal(my_parts[mop])) {
            my_main_operator = new TemporalOperator(my_parts[mop]);
            if (my_parts[mop+1].equals("[")) {
                mop2 = mop + 5;
                try{
                    ((TemporalOperator)my_main_operator).setInterval(Integer.parseInt(my_parts[mop+2]), Integer.parseInt(my_parts[mop+4]));
                } catch(NumberFormatException nfe) {
                    my_logger.error("Only interger is accepted in the Interval!");       
                }
                
                my_logger.info("Set Interval: " + my_main_operator.toString());
            } else {
                mop2 = mop;
            }
            my_is_temporal = true;
            my_is_firstorder = false;
        } else if (ReservedSymbol.isQuantifier(my_parts[mop])) {
            final Set<String> temp_set = new HashSet<String>();
            mop2 = mop + 1;
            for (int i = mop2; i < my_parts.length; i++) {
                if ("(".equals(my_parts[i])) {
                    mop2 = i - 1;
                    break;
                } else {
                    temp_set.add(my_parts[i]);
                    my_bound_variable.add(my_parts[i]);
                }
            }
            my_main_operator = new QuantifierOperator(my_parts[mop]);
            ((QuantifierOperator) my_main_operator).addVariable(temp_set);
        } else {
            mop2 = mop;
            my_main_operator = new FirstorderOperator(my_parts[mop]);
        }
        
        final String[] _parts1 = new String[mop];
        final String[] _parts2 = new String[my_parts.length - 1 - mop2];
        
        System.arraycopy(my_parts, 0, _parts1, 0, _parts1.length);
        System.arraycopy(my_parts, mop2 + 1, _parts2, 0, _parts2.length);
        
        my_logger.debug("********Part1**********");
        my_logger.debug(_parts1);

        my_logger.debug("********Part2**********");
        my_logger.debug(_parts2);
        my_logger.info("\n");
        
        if (_parts1.length > 0) {
            my_left_subformula = new TemporalFormula(_parts1);
        }
        if (_parts2.length > 0) {
            my_right_subformula = new TemporalFormula(_parts2);
        }
        
        if (my_left_subformula != null) {
            my_is_firstorder = my_is_firstorder && my_left_subformula.my_is_firstorder; 
        }
        if (my_right_subformula != null) {
            my_is_firstorder = my_is_firstorder && my_right_subformula.my_is_firstorder; 
        }
    }
    
    private int findMainOp() {
        my_logger.debug("InMethod: findMainOp");
        
        int pos = 0;
        int count = 0;
        
        do {
            if (my_parts[pos].equals("(")) {
                count += 1;
            } else if (my_parts[pos].equals(")")) {
                count -= 1;
            }
            pos++;
        } while ((count != 0) && (pos != my_parts.length));
        
        if (count != 0) {
            my_logger.fatal("Formula not well-formed (parenthesis do not match)");
        }
        
        //System.out.println("\n------------" + pos);
        for (pos = pos - 1; pos < my_parts.length; pos++) {
            if (ReservedSymbol.isOperator(my_parts[pos])) {
                break;
            }
        }
        
        if (pos == my_parts.length) {
            pos = -2;
        }
        
        // TEST
        my_logger.debug("Main Operator Position: " + pos);
        if (pos >= 0) {
            my_logger.info(my_parts[pos]);
        }
        
        return pos;
    }
    
    public void signatureExtension() {
        //TODO implement it
    }
    
    public void formulaTransformation() {
        //TODO implement it
    }
    
    /**
     * 
     */
    public String toString() {
        String temp_str = "";
        
        if (my_left_subformula != null) {
            temp_str = temp_str.concat("(").concat(my_left_subformula.toString()).concat(")");
        }
        
        if (my_main_operator != null) {
            temp_str = temp_str.concat(" ").concat(my_main_operator.toString()).concat(" ");
        }
        
        if (my_right_subformula != null) {
            temp_str = temp_str.concat("(").concat(my_right_subformula.toString()).concat(")");
        }
        
        return temp_str;
    }
}
