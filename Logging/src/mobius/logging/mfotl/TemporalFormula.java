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
    public TemporalFormula left = null;
    public TemporalFormula right = null;
    
    public AtomicFormula aleft = null;
    public AtomicFormula aright = null;

    /*
     * 
     */
    public Operator main_operator = null;
    public TemporalOperator temporal_operator = null;
    
    /*
     * check is this temporal formula is first order or not.
     */
    public boolean is_firstorder = false;
    public boolean is_true = false;
    
    private final Logger logger = new Logger();
    
    private String[] parts;

    public TemporalFormula(final String[] _parts) {
        parts = new String[_parts.length];
        System.arraycopy(_parts, 0, parts, 0, parts.length);
        
        parseFormula();
    }
    
    private String[] removeOuterParenthesis() {
        final String[] tmpparts = new String[parts.length-2];
        System.arraycopy(parts, 1, tmpparts, 0, tmpparts.length);
        
        for (int i = 0; i < tmpparts.length; i++) {
            logger.info(tmpparts[i]);
        }
        
        return tmpparts;
    }
    
    private final void parseFormula() {
        if (parts.length == 0) {
            return;
        }
        
        int mop = findMainOp();
        
        while ((mop == -2) && (parts[0].equals("("))) {
            logger.info("\nRemove outer most parenthesis");
            parts = removeOuterParenthesis();
            mop = findMainOp();
        }
        
        if (mop == -2) {
            logger.info("\nBuild atomic formula");
            
            aright = new AtomicFormula(parts);
            logger.info(aright.toString() + " -> ATOMIC FORMULA");
            
            is_firstorder = true;
        } else {
            // temporal_operator
            int mop2 = mop;
            if (parts[mop].equals("P") || parts[mop].equals("N") || parts[mop].equals("U") 
                    || parts[mop].equals("S") || parts[mop].equals("A")) {
                temporal_operator = new TemporalOperator(parts[mop]);
                if (parts[mop+1].equals("[")) {
                    mop2 = mop + 5;
                    temporal_operator.setInterval(Integer.parseInt(parts[mop+2]), Integer.parseInt(parts[mop+4]));
                    
                    logger.info("Set Interval: [" + temporal_operator.getStart() + ", " + temporal_operator.getEnd() + ")");
                }
                is_firstorder = false;
            } else {
                main_operator = new Operator(parts[mop]);
                is_firstorder = true;
            }
            
            final String[] _parts1 = new String[mop];
            final String[] _parts2 = new String[parts.length - mop2 - 1];
            
            System.arraycopy(parts, 0, _parts1, 0, _parts1.length);
            System.arraycopy(parts, mop2 + 1, _parts2, 0, _parts2.length);
            
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
            
            right = new TemporalFormula(_parts1);
            left = new TemporalFormula(_parts2);
            
            if (is_firstorder) {
                is_firstorder = right.is_firstorder & left.is_firstorder;
            }
        }
    }
    
    private int findMainOp() {
        int pos = 0, count = 0;
        
        for (; pos < parts.length; pos++) {
            if (parts[pos].equals("(")) {
                count += 1;
            } else if (parts[pos].equals(")")) {
                count -= 1;
            }
            
            if (count == 0)
                break;
        }
        
        if (count == 0) {
            //System.out.println("\n------------" + pos);
            for (; pos < parts.length; pos++) {
                if (Operator.OPER.containsKey(parts[pos])) {
                    break;
                }
            }
            
            if (pos == parts.length) {
                pos = -2;
            }
        } else {
            pos = -3;
        }
        
        // TEST
        if (pos >= 0) {
            logger.info("\nMainOP " + pos);
            logger.info(parts[pos]);
        }
        else
            logger.info("\nNoMainOP " + pos);
        return pos;
    }
}
