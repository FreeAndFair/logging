package mobius.logging.mfotl;

import java.util.Set;

// TODO Implement the full algorithm

public class Monitor {
    // Attributes
    final private MFOTLFormula my_formula;
    private MFOTLFormula my_formula_hat;
    private Signature my_signature;
    final private Logger my_logger = new Logger();
    
    final private TemporalStructure my_ats;
    private static int my_auxiliary_index = 0;
    
    // Constructors
    //@ assignable my_signature;
    //@ assignable my_formula;
    public Monitor(final /*@ non_null @*/ String a_formula, final /*@ non_null @*/ Signature a_signature) {
        my_signature = a_signature;
        my_formula = new MFOTLFormula(a_formula, my_signature);
        my_ats = new TemporalStructure();
    }
    
    // Public Methods

    /**
     * The main monitoring algorithm
     * (MFOTL, Basin et al., page 10)
     * @param a_temporalstructure
     */
    public void runMonitor(final /*@ non_null @*/ TemporalStructure a_temporalstructure) {
        Structure my_auxiliary_structure;
        // i: current index in input sequence (D0, t0)...
        int q = 0; // index of next query evaluation in sequence (D0, t0) ...
        Q q_0 = new Q(my_formula.my_formula);

        // Copy original structure for extension
        for (int i = 0; i < a_temporalstructure.getSize(); i++) {
            my_auxiliary_structure = new Structure ((Structure) a_temporalstructure.my_structure.get(i));
            my_ats.insertStructure(my_auxiliary_structure, a_temporalstructure.my_time_stamp.get(i));
        }
        
        // Signature, Structure Extension & Formula Transformation
        for (int i = 0; i < a_temporalstructure.getSize(); i++) {
            my_logger.debug("Before Formula Transformation!");
            my_logger.debug(a_temporalstructure.my_structure.get(i).toString());
            
            my_auxiliary_structure = my_ats.my_structure.get(i);

            my_logger.debug("Before Signature Extension & Formula Transformation----------");
            my_logger.debug(my_formula.my_formula.toString());
            
            transformFormula(a_temporalstructure, i);
            
            my_logger.debug("After Signature Extension & Formula Transformation----------");
            my_logger.debug(my_formula_hat.my_formula.toString());
        }
        
        for (int i = 0; i < my_ats.getSize(); i++) {
        //for (int i = 0; i < 1; i++) {
            my_logger.debug("Start Evaluating Formula..........");
            my_auxiliary_structure = my_ats.my_structure.get(i);
            my_logger.debug(my_auxiliary_structure.toString());
            if (my_formula_hat.evaluate(my_auxiliary_structure)){
                // True returned, continue evaluating
            } else {
                // TODO reconstruct Q
                q++;
            }
            my_logger.debug("End Evaluating Formula..........");
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
	        transformTemporalSubformula(my_formula_hat.my_formula, a_pos);
	    }
	}
	
	/**
	 * transform temporal sub-formula 
	 * @param a_formula
	 * @param a_ts
	 * @param a_pos
	 */
	private void transformTemporalSubformula(final /*@ non_null @*/ Formula a_formula,
	        final int a_pos) {
	    if (a_formula == null || a_formula instanceof AtomicFormula) {
	        return;
	    } else if (a_formula.my_is_temporal) {
	        Structure my_auxiliary_structure = my_ats.my_structure.get(a_pos);
	        
	        final Set<String> temp_var = ((TemporalFormula) a_formula).getFreeVariable();
	        final String[] temp_var2 = new String[temp_var.size()];
	        int j = 0;
	        // TODO BUG: Set & Array position 
	        for (String i: temp_var) {
	            temp_var2[j++] = i;
	        }
	        
	        String temp_formula_name = "p" + my_auxiliary_index;
	        my_auxiliary_index ++;
	        my_signature.addPredicate(new Predicate(temp_formula_name, temp_var2.length));
	        
	        ((TemporalFormula) a_formula).my_auxiliary_predicate = new AtomicFormula(temp_var2, temp_var2.length, 
	                temp_formula_name, my_signature);
	        
	        my_auxiliary_structure.initRelationAssign(temp_formula_name);
	        
	        if (((TemporalFormula) a_formula).my_main_operator.my_name.equals("P")) {
	            // TODO improve it to non-atomic ones
	            if (a_pos == 0) {
	                return;
	            }
	            
                int temp_time_interval = my_ats.my_time_stamp.get(a_pos) - my_ats.my_time_stamp.get(a_pos-1); 
                if (((TemporalOperator)((TemporalFormula) a_formula).my_main_operator).inRange(temp_time_interval)) {
                    my_logger.fatal("Security Policy breach!");
                }
                Set<int[]> temp_ra = my_ats.my_structure.get(a_pos-1).getRelationAssign(
                        ((AtomicFormula) 
                                ((TemporalFormula) a_formula).my_right_subformula).my_predicate.getSymbol());
                my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_ra);
	        } else if (((TemporalFormula) a_formula).my_main_operator.my_name.equals("N")) {
                int temp_time_interval = my_ats.my_time_stamp.get(a_pos+1) - my_ats.my_time_stamp.get(a_pos); 
                if (((TemporalOperator)((TemporalFormula) a_formula).my_main_operator).inRange(temp_time_interval)) {
                    my_logger.fatal("Security Policy breach!");
                }
                Set<int[]> temp_ra = my_ats.my_structure.get(a_pos+1).getRelationAssign(temp_formula_name);
                my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_ra);
	        }
	    } else {
	        transformTemporalSubformula(((TemporalFormula) a_formula).my_left_subformula, a_pos);
	        transformTemporalSubformula(((TemporalFormula) a_formula).my_right_subformula, a_pos);
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
