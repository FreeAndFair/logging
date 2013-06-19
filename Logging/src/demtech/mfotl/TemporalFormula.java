package demtech.mfotl;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

public class TemporalFormula extends Formula{
    // Attributes
    private Formula my_left_subformula;
    private Formula my_right_subformula;
    private Operator my_main_operator;    
    final private AtomicFormula[] my_auxiliary_predicate;
    
    final private List<String> my_free_variable = new LinkedList();
    final private Set<String> my_bound_variable = new HashSet();
    final private Set<String> my_variable = new HashSet();
    
    final private Signature my_signature;
    private String[] my_tokens;
    private static final Logger my_logger = new Logger(false);
    
    // Constructor
    public TemporalFormula(final String[] a_tokens, final Signature a_signature) {
        super();
        
        my_signature = a_signature;
        my_tokens = new String[a_tokens.length];
        System.arraycopy(a_tokens, 0, my_tokens, 0, my_tokens.length);
        my_auxiliary_predicate = new AtomicFormula[3];
        
        if (my_tokens.length == 0) {
            my_logger.info("Temporal Formula with length 0");
        } else {
            my_logger.debug("In Formula: ");
            my_logger.debug(a_tokens);
        }
    }
    
    // Public Methods
    public void init() {
        parseFormula();
        
        for (String i : my_variable) {
            if (!my_bound_variable.contains(i)) {
                my_free_variable.add(i);
            }
        }
        
        my_logger.debug("????????? All Variables (Constants): " +  my_variable);
        my_logger.debug("Bound Variables: " + my_bound_variable);
        my_logger.debug("Free Variables: " + my_free_variable);
    }
    
    public /*@ pure @*/ List<String> getFreeVariable() {
        return my_free_variable;
    }
    
    public /*@ pure @*/ Set<TemporalFormula> getTemporalSubformula(final Formula a_formula) {
        if (a_formula == null) {
            return null;
        }
        
        Set<TemporalFormula> my_temporal_subformula = new HashSet();
        
        if (a_formula.my_is_temporal) {
            my_temporal_subformula.add((TemporalFormula) a_formula);
        } else if (a_formula instanceof TemporalFormula) {
                Set<TemporalFormula> tsubl = getTemporalSubformula(((TemporalFormula) a_formula).my_left_subformula);
                my_temporal_subformula.addAll(tsubl);
                Set<TemporalFormula> tsubr = getTemporalSubformula(((TemporalFormula) a_formula).my_right_subformula);
                my_temporal_subformula.addAll(tsubr);
        }
        
        return my_temporal_subformula;
    }
    

    
    /**
     * When the <code>evaluate()</code> method is called, the temporal sub-formula is
     * already replaced with first order formulas after formula tranformation.
     */
    protected Evaluation evaluate(final Structure a_structure) {
        my_logger.debug("InMethod: TemporalFormula.evaluate");
        Evaluation result_eval = new Evaluation(this.my_free_variable);
        
        if (my_auxiliary_predicate[0] != null) { // Temporal Formula transformed
            result_eval = my_auxiliary_predicate[0].evaluate(a_structure);
        } else if (my_main_operator == null) { // Atomic Formula
            result_eval = my_right_subformula.evaluate(a_structure);
        } else if ("&".equals(my_main_operator.my_name)) { // First Order Formula &
            result_eval = my_left_subformula.evaluate(a_structure);
            result_eval.conjunction(my_right_subformula.evaluate(a_structure));
        } else if ("!".equals(my_main_operator.my_name)) { // First Order Formula !
            result_eval = my_right_subformula.evaluate(a_structure);
            result_eval.negation();
        } else if ("E".equals(my_main_operator.my_name)) { // First Order Formula E
            my_logger.debug("Check Existential " + my_right_subformula.toString());
            result_eval = my_right_subformula.evaluate(a_structure);
            result_eval.removeBoundVar(((QuantifierOperator) my_main_operator).getBoundVariables());
        }
        
        return result_eval;
    }
    
    public boolean evaluateTruth(final Structure a_structure) { // if no free variable exists
        if (a_structure == null) {
            return false;
        }
        
        final Evaluation a_val = this.evaluate(a_structure);
        
        my_logger.debug(a_val.toString());
        
        return a_val.isTrue();
    }
    
    // Private Methods
    //@ assignable my_tokens;
    private void removeOuterParenthesis() {
        final String[] tmpparts = new String[my_tokens.length-2];
        
        my_logger.info("\nRemove outer most parenthesis");
        
        if (my_tokens[0].equals("(") && my_tokens[my_tokens.length-1].equals(")")) {
            System.arraycopy(my_tokens, 1, tmpparts, 0, tmpparts.length);
        } else {
            my_logger.error("Remove outer most parenthesis ERROR!!!");
        }
        
        my_tokens = tmpparts;
    }

    //@ pure
    private void parseFormula() {
        my_logger.debug("InMethod: parseFormula");
        int mop = findMainOp();
        
        /**
         * if no main operator is found, then either it has a outer most parenthesis
         * or it is an atomic formula
         */
        while ((mop == -2) && (my_tokens[0].equals("("))) {
            removeOuterParenthesis();
            mop = findMainOp();
        }
        
        if (mop == -2) {
            parseAtomicFormula();
        } else {
            parseTemporalFormula(mop);
        }
    }
    
    //@ assignable my_right_subformula
    private void parseAtomicFormula() {
        my_right_subformula = new AtomicFormula(my_tokens, my_signature);
        my_variable.addAll(((AtomicFormula)my_right_subformula).getFreeVariable());
    }
    
    private void parseTemporalFormula(final int mop) {
        int mop2;
        if (ReservedSymbol.isTemporal(my_tokens[mop])) {
            my_main_operator = new TemporalOperator(my_tokens[mop]);
            if (my_tokens[mop+1].equals("[")) {
                mop2 = mop + 5;
                try{
                    ((TemporalOperator)my_main_operator).setInterval(Integer.parseInt(my_tokens[mop+2]), Integer.parseInt(my_tokens[mop+4]));
                } catch(NumberFormatException nfe) {
                    my_logger.error("Only interger is accepted in the Interval!");       
                }
                
                my_logger.info("Set Interval: " + my_main_operator.toString());
            } else {
                mop2 = mop;
            }
            my_is_temporal = true;
            my_is_firstorder = false;
        } else if (ReservedSymbol.isQuantifier(my_tokens[mop])) {
            final Set<String> temp_set = new HashSet<String>();
            mop2 = mop + 1;
            for (int i = mop2; i < my_tokens.length; i++) {
                if ("(".equals(my_tokens[i])) {
                    mop2 = i - 1;
                    break;
                } else {
                    temp_set.add(my_tokens[i]);
                    my_bound_variable.add(my_tokens[i]);
                }
            }
            my_main_operator = new QuantifierOperator(my_tokens[mop]);
            ((QuantifierOperator) my_main_operator).addVariable(temp_set);
        } else {
            mop2 = mop;
            my_main_operator = new FirstorderOperator(my_tokens[mop]);
        }
        
        final String[] token_parts1 = new String[mop];
        final String[] token_parts2 = new String[my_tokens.length - 1 - mop2];
        
        System.arraycopy(my_tokens, 0, token_parts1, 0, token_parts1.length);
        System.arraycopy(my_tokens, mop2 + 1, token_parts2, 0, token_parts2.length);
        
        my_logger.debug("********Part1**********");
        my_logger.debug(token_parts1);

        my_logger.debug("********Part2**********");
        my_logger.debug(token_parts2);
        my_logger.info("\n");
        
        if (token_parts1.length > 0) {
            my_left_subformula = new TemporalFormula(token_parts1, my_signature);
            ((TemporalFormula)my_left_subformula).init();
            
            my_bound_variable.addAll(((TemporalFormula) my_left_subformula).my_bound_variable);
            my_variable.addAll(my_bound_variable);
            my_variable.addAll(((TemporalFormula) my_left_subformula).my_variable);
            my_is_firstorder &= my_left_subformula.my_is_firstorder;
        }
        if (token_parts2.length > 0) {
            my_right_subformula = new TemporalFormula(token_parts2, my_signature);
            ((TemporalFormula)my_right_subformula).init();
            
            my_bound_variable.addAll(((TemporalFormula) my_right_subformula).my_bound_variable);
            my_variable.addAll(my_bound_variable);
            my_variable.addAll(((TemporalFormula) my_right_subformula).my_variable);
            
            my_is_firstorder &= my_right_subformula.my_is_firstorder; 
        }
    }
    
    //@ pure
    private int findMainOp() {
        my_logger.debug("InMethod: findMainOp");
        
        int pos = 0;
        int count = 0;
        
        do {
            if (my_tokens[pos].equals("(")) {
                count += 1;
            } else if (my_tokens[pos].equals(")")) {
                count -= 1;
            }
            pos++;
        } while ((count != 0) && (pos != my_tokens.length));
        
        if (count != 0) {
            my_logger.fatal("Formula not well-formed (parenthesis do not match)");
        }
        
        for (pos = pos - 1; pos < my_tokens.length; pos++) {
            if (ReservedSymbol.isOperator(my_tokens[pos])) {
                break;
            }
        }
        
        if (pos == my_tokens.length) {
            pos = -2;
        }
        
        my_logger.debug("Main Operator Position: " + pos);
        if (pos >= 0) {
            my_logger.info(my_tokens[pos]);
        }
        
        return pos;
    }
    
    public /*@ pure @*/ Formula getLeftSubformula() {
        return this.my_left_subformula;
    }
    
    public /*@ pure @*/ Formula getRightSubformula() {
        return this.my_right_subformula;
    }
    
    public TemporalFormula getLeftTemporalSub() {
        if (this.my_left_subformula instanceof TemporalFormula && 
                ((TemporalFormula)this.my_left_subformula).my_main_operator != null) {
            return (TemporalFormula) this.my_left_subformula;
        } else {
            return null;
        }
    }

    public TemporalFormula getRightTemporalSub() {
        if (this.my_right_subformula instanceof TemporalFormula && 
                ((TemporalFormula)this.my_right_subformula).my_main_operator != null) {
            return (TemporalFormula) this.my_right_subformula;
        } else {
            return null;
        }
    }
    
    public AtomicFormula getAtomicSub() {
        if (this.my_main_operator == null && this.my_right_subformula instanceof AtomicFormula) {
            return (AtomicFormula)this.my_right_subformula;
        } else {
            return null;
        }
    }
    
    public /*@ pure @*/ Operator getMainOperator() {
        return this.my_main_operator;
    }
    
    public /*@ pure @*/ AtomicFormula getAuxiliaryFormula(final int a_int) {
        if (a_int < 3) {
            return this.my_auxiliary_predicate[a_int];
        } else {
            return null;
        }
    }
    
    public void setAuxiliaryFormula(final int a_int, final AtomicFormula a_atomic_formula) {
        if (a_int <3) {
            this.my_auxiliary_predicate[a_int] = a_atomic_formula;
        }
    }
    
    public String toString() {
        String temp_str = "";
        
        if (my_auxiliary_predicate[0] != null) {
            temp_str = my_auxiliary_predicate[0].toString();
            if (my_auxiliary_predicate[1] != null) {
                temp_str = temp_str.concat(my_auxiliary_predicate[1].toString());
            }
            if (my_auxiliary_predicate[2] != null) {
                temp_str = temp_str.concat(my_auxiliary_predicate[2].toString());
            }
            return temp_str;
        }
        
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