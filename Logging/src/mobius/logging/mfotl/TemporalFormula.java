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
    public boolean is_true = false;
    
    public static Set my_bound_variable = new HashSet();
    public static Set<String> my_variable = new HashSet();
    // TODO add collection of variables;
    
    private final Logger logger = new Logger();
    
    private String[] my_parts;

    public TemporalFormula(final String[] _parts) {
        my_parts = new String[_parts.length];
        System.arraycopy(_parts, 0, my_parts, 0, my_parts.length);
        
        if (my_parts.length == 0) {
            logger.info("Temporal Formula with length 0");
        } else {
            parseFormula();
        }
    }
    
    private void removeOuterParenthesis() {
        final String[] tmpparts = new String[my_parts.length-2];
        
        logger.info("\nRemove outer most parenthesis");        
        if (my_parts[0].equals("(") && my_parts[my_parts.length-1].equals(")")) {
            System.arraycopy(my_parts, 1, tmpparts, 0, tmpparts.length);
        } else {
            logger.error("Remove outer most parenthesis ERROR!!!");
        }
        
        my_parts = tmpparts;
    }

    /**
     * 
     */
    private final void parseFormula() {
        logger.debug("InMethod: parseFormula");
        
        int mop = findMainOp();
        
        while ((mop == -2) && (my_parts[0].equals("("))) {
            removeOuterParenthesis();
            mop = findMainOp();
        }
        
        if (mop == -2) {
            my_right_subformula = new AtomicFormula(my_parts);

            logger.debug(my_right_subformula.toString() + " -> ATOMIC FORMULA");
            return;
        }
        
        // non atomic formula
        int mop2;
        if (ReservedSymbol.isTemporal(my_parts[mop])) {
            my_main_operator = new TemporalOperator(my_parts[mop]);
            if (my_parts[mop+1].equals("[")) {
                mop2 = mop + 5;
                ((TemporalOperator)my_main_operator).setInterval(Integer.parseInt(my_parts[mop+2]), Integer.parseInt(my_parts[mop+4]));
                
                logger.info("Set Interval: [" + ((TemporalOperator)my_main_operator).getStart() + ", " + ((TemporalOperator)my_main_operator).getEnd() + ")");
            } else {
                mop2 = mop;
            }
            is_temporal = true;
            is_firstorder = false;
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
        
        logger.debug("********Part1**********");
        logger.debug(_parts1);

        logger.debug("********Part2**********");
        logger.debug(_parts2);
        logger.info("\n");
        
        if (_parts1.length > 0) {
            my_left_subformula = new TemporalFormula(_parts1);
        }
        if (_parts2.length > 0) {
            my_right_subformula = new TemporalFormula(_parts2);
        }
        
        if (my_left_subformula != null) {
            is_firstorder = is_firstorder && my_left_subformula.is_firstorder; 
        }
        if (my_right_subformula != null) {
            is_firstorder = is_firstorder && my_right_subformula.is_firstorder; 
        }
    }
    
    private int findMainOp() {
        logger.debug("InMethod: findMainOp");
        
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
            logger.fatal("Formula not well-formed (parenthesis do not match)");
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
        logger.debug("Main Operator Position: " + pos);
        if (pos >= 0) {
            logger.info(my_parts[pos]);
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
