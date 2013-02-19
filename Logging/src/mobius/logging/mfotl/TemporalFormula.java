package mobius.logging.mfotl;

//TODO add specs and docs


/*
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
            int mop2 = mop;
            if (Operator.isTemporal(my_parts[mop])) {
                my_temporal_operator = new TemporalOperator(my_parts[mop]);
                if (my_parts[mop+1].equals("[")) {
                    mop2 = mop + 5;
                    my_temporal_operator.setInterval(Integer.parseInt(my_parts[mop+2]), Integer.parseInt(my_parts[mop+4]));
                    
                    logger.info("Set Interval: [" + my_temporal_operator.getStart() + ", " + my_temporal_operator.getEnd() + ")");
                }
                is_firstorder = false;
            } else {
                my_main_operator = new Operator(my_parts[mop]);
                is_firstorder = true;
            }
            
            final String[] _parts1 = new String[mop];
            final String[] _parts2 = new String[my_parts.length - mop2 - 1];
            
            System.arraycopy(my_parts, 0, _parts1, 0, _parts1.length);
            System.arraycopy(my_parts, mop2 + 1, _parts2, 0, _parts2.length);
            
            logger.info("********Part1**********");
            for (int i = 0; i < _parts1.length; i++) {
                logger.info(_parts1[i]);
            }
            logger.info("\n");
            logger.info("********Part2**********");
            for (int i = 0; i < _parts2.length; i++) {
                logger.info(_parts2[i]);
            }
            logger.info("\n");
            
            my_right = new TemporalFormula(_parts1);
            my_left = new TemporalFormula(_parts2);
            
            if (is_firstorder) {
                is_firstorder = my_right.is_firstorder & my_left.is_firstorder;
            }
        }
    }
    
    private int findMainOp() {
        int pos = 0;
        int count = 0;
        
        do {
            if (my_parts[pos].equals("(")) {
                count += 1;
                pos++;
            } else if (my_parts[pos].equals(")")) {
                count -= 1;
                pos++;
            }
        } while ((count != 0) && (pos != my_parts.length));
        
        if (count != 0) {
            logger.fatal("Formula not well-formed (parenthesis do not match)");
        }
        
        //System.out.println("\n------------" + pos);
        for (; pos < my_parts.length; pos++) {
            if (Operator.isTemporal(my_parts[pos]) || Operator.isFirstOrder(my_parts[pos])) {
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
