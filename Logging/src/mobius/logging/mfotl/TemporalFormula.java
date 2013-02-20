package mobius.logging.mfotl;

import java.util.HashSet;
import java.util.Set;

//TODO add specs and docs


/**
 * Temporal Formula
 */
public class TemporalFormula {
    /*
     * TemporalFormula ::= AtomicFormula
     * TemporalFormula ::= TemporalFormula + Operator + TemporalFormula
     */
    public TemporalFormula my_left = null;
    public TemporalFormula my_right = null;
    
    public AtomicFormula my_atomic_left = null;
    public AtomicFormula my_atomic_right = null;

    /**
     * 
     */
    public Operator my_main_operator = null;
    public TemporalOperator my_temporal_operator = null;
    
    /**
     * check is this temporal formula is first order or not.
     */
    public boolean is_firstorder = false;
    public boolean is_true = false;
    
    public static Set bound_variable = new HashSet();
    
    private final Logger logger = new Logger();
    
    private String[] my_parts;

    public TemporalFormula(final String[] _parts) {
        new Operator();
        
        my_parts = new String[_parts.length];
        System.arraycopy(_parts, 0, my_parts, 0, my_parts.length);
        
        if (my_parts.length == 0) {
            logger.info("Temporal Formula with length 0");
        } else {
            parseFormula();
        }
    }
    
    private String[] removeOuterParenthesis() {
        final String[] tmpparts = new String[my_parts.length-2];
        
        logger.info("\nRemove outer most parenthesis");        
        if (my_parts[0].equals("(") && my_parts[my_parts.length-1].equals(")")) {
            System.arraycopy(my_parts, 1, tmpparts, 0, tmpparts.length);
        } else {
            logger.error("Remove outer most parenthesis ERROR!!!");
        }
        
        return tmpparts;
    }

    /**
     * 
     */
    private final void parseFormula() {
        logger.debug("InMethod: parseFormula");
        
        int mop = findMainOp();
        
        while ((mop == -2) && (my_parts[0].equals("("))) {
            my_parts = removeOuterParenthesis();
            mop = findMainOp();
        }
        
        if (mop == -2) {
            my_atomic_right = new AtomicFormula(my_parts);

            logger.debug(my_atomic_right.toString() + " -> ATOMIC FORMULA");
            
            is_firstorder = true;
        } else {
            // temporal_operator
            int mop2;
            if (Operator.isTemporal(my_parts[mop])) {
                my_temporal_operator = new TemporalOperator(my_parts[mop]);
                if (my_parts[mop+1].equals("[")) {
                    mop2 = mop + 5;
                    my_temporal_operator.setInterval(Integer.parseInt(my_parts[mop+2]), Integer.parseInt(my_parts[mop+4]));
                    
                    logger.info("Set Interval: [" + my_temporal_operator.getStart() + ", " + my_temporal_operator.getEnd() + ")");
                } else {
                    mop2 = mop;
                }
                is_firstorder = false;
            } else {
                mop2 = mop;
                my_main_operator = new Operator(my_parts[mop]);
                is_firstorder = true;
            }
            
            final String[] _parts1 = new String[mop];
            final String[] _parts2 = new String[my_parts.length - mop2 - 1];
            
            System.arraycopy(my_parts, 0, _parts1, 0, _parts1.length);
            System.arraycopy(my_parts, mop2 + 1, _parts2, 0, _parts2.length);
            
            logger.debug("********Part1**********");
            logger.debug(_parts1);

            logger.debug("********Part2**********");
            logger.debug(_parts2);
            logger.info("\n");
            
            my_right = new TemporalFormula(_parts1);
            my_left = new TemporalFormula(_parts2);
            
            if (is_firstorder) {
                is_firstorder = my_right.is_firstorder & my_left.is_firstorder;
            }
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
            if (Operator.isOperator(my_parts[pos])) {
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
}
