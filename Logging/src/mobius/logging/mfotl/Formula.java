package mobius.logging.mfotl;

public class Formula {
    private final String original_formula;
    protected String[] formula_parts;

    protected String[] freevar;
    
    public TemporalFormula temporal_formula;
    public TemporalFormula[] temporal_subformula;
    
    public Structure structure;
    
    public Formula(final String _formula) {
        new Operator(); // Initializing the Operator
        
        original_formula = _formula;
        lexer(original_formula);

        println("Read Formula: " + original_formula + ". With Length " + formula_parts.length);
        
        temporal_formula = new TemporalFormula(formula_parts);
        
        println("");

        getTemporalSubformula();
        getFreeVar();
    }
    
    
    // review Jian
    public boolean evaluation(Structure structure) {
        return true;
    }
    
    /*
     * <p>
     * Get the temporal subformula
     * </p>
     */
    private void getTemporalSubformula() {
        temporal_subformula = new TemporalFormula[5];
        
        System.out.println();
    }
	
	private void getFreeVar() {
	    System.out.println();
	}
	
	private void println(String _str) {
	    System.out.println(_str);
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
            char character = formula_str.charAt(i);
            
//            System.out.println("------------->>>>>" + formulaWSpace);
            
            if ((character == '(') || (character == ')')
                    || (character == '[') || (character == ',')
                    || (character == '=') || (character == '<')
                    || (character == ' ')
                    || Operator.OPER.containsKey(Character.toString(character))) {
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
                    System.out.println("Illegal Letter in Formula!!!");
                    System.exit(0);
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
                System.out.println("EMPTY FORMULA!!!");
                System.exit(0);
            }
        }
        
        formula_str = formulaWSpace.replaceAll("[ ]+", " ");
        System.out.println("Formula with Space: " + formula_str);
        formula_parts = formula_str.split(" ");
        
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

/*
 * Class Atomic_Formula
 * 
 * for the leave notes of formula
 */

class AtomicFormula {
    protected Predicate operator;
    
    public AtomicFormula(String[] _var, int _arity, String _operator) {
        operator = new Predicate(_operator, _arity, _var);
    }
    
    public AtomicFormula(String[] _formula) {
        if (_formula[1].equals("=") || _formula[1].equals("<")) {
            final String[] _var_tmp = {_formula[0], _formula[2]};
            operator = new Predicate(_formula[1], 2, _var_tmp);
        } else {
            String[] _var_tmp = new String[(_formula.length-2)/2];
            for (int i = 0; i < _var_tmp.length; i++) {
                _var_tmp[i] = _formula[(i+1)*2];
            }
            operator = new Predicate(_formula[0], _var_tmp.length , _var_tmp);
        }
    }
    
    public String toString() {
        return operator.toString();
    }
}

class TemporalFormula {
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
            System.out.print(tmpparts[i]);
        }
        
        return tmpparts;
    }
    
    private final void parseFormula() {
        int mop = 0;
        
        if (parts.length == 0) {
            return;
        }
        
        mop = findMainOp();
        
        while ((mop == -2) && (parts[0].equals("("))) {
            System.out.println("\nRemove outer most parenthesis");
            parts = removeOuterParenthesis();
            mop = findMainOp();
        }
        
        if (mop == -2) {
            System.out.println("\nBuild atomic formula");
            
            aright = new AtomicFormula(parts);
            System.out.println(aright.toString() + " -> ATOMIC FORMULA");
            
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
                    
                    System.out.println("Set Interval: [" + temporal_operator.getStart() + ", " + temporal_operator.getEnd() + ")");
                }
                is_firstorder = false;
            } else {
                main_operator = new Operator(parts[mop]);
                is_firstorder = true;
            }
            
            String[] _parts1 = new String[mop];
            String[] _parts2 = new String[parts.length - mop2 - 1];
            
            System.arraycopy(parts, 0, _parts1, 0, _parts1.length);
            System.arraycopy(parts, mop2 + 1, _parts2, 0, _parts2.length);
            
            System.out.println("********Part1**********");
            for (int i = 0; i < _parts1.length; i++) {
                System.out.print(_parts1[i]);
            }
            System.out.println("\n");
            System.out.println("********Part2**********");
            for (int i = 0; i < _parts2.length; i++) {
                System.out.print(_parts2[i]);
            }
            System.out.println("\n");
            
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
            System.out.println("\nMainOP " + pos);
            System.out.println(parts[pos]);
        }
        else
            System.out.println("\nNoMainOP " + pos);
        return pos;
    }
}