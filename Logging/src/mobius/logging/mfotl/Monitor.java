package mobius.logging.mfotl;

import java.util.Set;

// TODO Implement the full algorithm

public class Monitor {
    // Attributes
    final private MFOTLFormula my_formula;
    private MFOTLFormula my_formula_hat;
    private Signature my_signature;
    final private Logger my_logger = new Logger();
    
    private static int my_auxiliary_index = 0;
    private Structure my_auxiliary_structure;
    
    // Constructors
    
    //@ assignable my_formula;
    public Monitor(final /*@ non_null @*/ String a_formula, final /*@ non_null @*/ Signature a_signature) {
        my_signature = a_signature;
        my_formula = new MFOTLFormula(a_formula, my_signature);
    }
    
    // Public Methods

    /**
     * the main monitor algorithm
     * (MFOTL, Basin et al., page 10)
     */
    public void runMonitor(final /*@ non_null @*/ TemporalStructure a_structure_sequence) {
        // i: current index in input sequence (D0, t0)...
        int q = 0; // index of next query evaluation in sequence (D0, t0) ...
        Q q_0 = new Q(my_formula.my_formula);
        
        for (int i = 0; i < a_structure_sequence.my_structure.size(); i++) {
        //for (int i = 0; i < 1; i++) {
            // carry over constants and relations of D_i to D'_i
            my_logger.debug("Before Formula Transformation!");
            my_logger.debug(((Structure) a_structure_sequence.my_structure.get(i)).toString());
            
            my_auxiliary_structure = new Structure ((Structure) a_structure_sequence.my_structure.get(i));

            transformFormula(a_structure_sequence, i);
            
            my_logger.debug("After Signature Extension & Formula Transformation");
            my_logger.debug(my_formula_hat.my_formula.toString());
            my_logger.debug(my_formula.my_formula.toString());
            my_logger.debug(my_formula_hat.toString());
            my_logger.debug(my_formula.toString());
            
            my_logger.debug("Start Evaluate Formula...");
            my_logger.debug(my_auxiliary_structure.toString());
            if (my_formula_hat.evaluate(my_auxiliary_structure)) {
                // TODO exit here, complete implementation
            } else {
                // TODO reconstruct Q
                q++;
            }
        }
    }

    // Private Methods
	/**
	 * transform formula
	 * @param a_ts
	 * @param a_pos
	 */
	//@ assignable my_formula_hat
	private void transformFormula(final /*@ non_null @*/ TemporalStructure a_ts, final int a_pos) {
	    my_formula_hat = new MFOTLFormula(my_formula, my_signature);
	    
	    if (my_formula_hat.my_formula.my_is_temporal) {
	        transformTemporalSubformula(my_formula_hat.my_formula, a_ts, a_pos);
	    }
	}
	
	/**
	 * transform temporal sub-formula 
	 * @param a_formula
	 * @param a_ts
	 * @param a_pos
	 */
	private void transformTemporalSubformula(final /*@ non_null @*/ Formula a_formula,
	        final TemporalStructure a_ts, final int a_pos) {
	    if (a_formula == null || a_formula instanceof AtomicFormula) {
	        return;
	    } else if (a_formula.my_is_temporal) {
	        final Set<String> temp_var = ((TemporalFormula) a_formula).getFreeVariable();
	        final String[] temp_var2 = new String[temp_var.size()];
	        int j = 0;
	        for (String i: temp_var) {
	            temp_var2[j++] = i;
	        }
	        
	        String temp_formula_name = "p" + my_auxiliary_index;
	        my_auxiliary_index ++;
	        ((TemporalFormula) a_formula).my_auxiliary_predicate = new AtomicFormula(temp_var2, temp_var2.length, 
	                temp_formula_name, my_signature);
	        
	        my_auxiliary_structure.initRelationAssign(temp_formula_name);
	        
	        if (((TemporalFormula) a_formula).my_main_operator.my_name.equals("P")) {
	            // TODO improve it to non-atomic ones
                int temp_time_interval = a_ts.my_time_stamp.get(a_pos) - a_ts.my_time_stamp.get(a_pos-1); 
                if (((TemporalOperator)((TemporalFormula) a_formula).my_main_operator).inRange(temp_time_interval)) {
                    // TODO detailed return value
                    return;   
                }
                Set<int[]> temp_ra = a_ts.my_structure.get(a_pos-1).getRelationAssign(temp_formula_name);
                my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_ra);
	        } else if (((TemporalFormula) a_formula).my_main_operator.my_name.equals("N")) {
                int temp_time_interval = a_ts.my_time_stamp.get(a_pos+1) - a_ts.my_time_stamp.get(a_pos); 
                if (((TemporalOperator)((TemporalFormula) a_formula).my_main_operator).inRange(temp_time_interval)) {
                    // TODO detailed return value
                    return;   
                }
                Set<int[]> temp_ra = a_ts.my_structure.get(a_pos+1).getRelationAssign(temp_formula_name);
                my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_ra);
	        }
	    } else {
	        transformTemporalSubformula(((TemporalFormula) a_formula).my_left_subformula, a_ts, a_pos);
	        transformTemporalSubformula(((TemporalFormula) a_formula).my_right_subformula, a_ts, a_pos);
	    }
	}

	private void extendSignature() {
        /*
         * R' = R Union {P_a|a temporal sub-formula of phi}
         */
        Set<TemporalFormula> temp_temporal_subformula = my_formula.getTemporalSubformula();
        
        for (TemporalFormula i : temp_temporal_subformula) {
            /*
             * Built new relation from temporal subformula (MFOTL, Basin et al., page 5)
             */
            my_logger.debug("Temporal Free Var: ");
            my_logger.debug(i.getFreeVariable());
            
            createAuxiliaryPredicate(i);
        }
    }
    

	private void createAuxiliaryPredicate(TemporalFormula a_temporal_formula) {
	    Set<String> temp_free_var = a_temporal_formula.getFreeVariable();
	    String[] temp_freevar_array = new String[temp_free_var.size()];
	    
	    int j = 0;
	    for (String i: temp_free_var) {
	        temp_freevar_array[j++] = i;
	    }
	    // Create p_alpha
	    Predicate temp_p_predicate = new Predicate("p", temp_free_var.size());
	    
	    if (a_temporal_formula.my_main_operator.my_name.equals("U")) { // create r_alpha, s_alpha
	        
	    } else if (a_temporal_formula.my_main_operator.my_name.equals("S")) { // create r_alpha
	        
	    }
	}
	
	// internal class
	/**
	 * <p>
	 * <code>Q</code> is designed according to the paper, page 8
	 * </p>
	 */
	class Q {
	    // Attribute
	    public TemporalFormula my_a;     // alpha temporal sub-formula of phi
	    public int my_i;              // index
	    public Set<TemporalFormula> my_w;     // waitfor(a)
	    
	    // Constructor
	    public Q(final TemporalFormula a_formula) {
	        my_a = a_formula;
	        my_i = 0;
	        my_w = waitfor(a_formula);
	    }
	    
	    public Q(final TemporalFormula a_formula, final int a_index) {
	        my_a = a_formula;
	        my_i = a_index;
	        my_w = waitfor(a_formula);
	    }
	    
	    // Private Method
	    private Set waitfor(final TemporalFormula a_formula) {
	        return null;
	    }
	}
}
