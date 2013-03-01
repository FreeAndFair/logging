package mobius.logging.mfotl;

import java.util.Set;

// TODO Implement the full algorithm

public class Monitor {
    // Attributes
    final private MFOTLFormula my_formula;
    private MFOTLFormula my_formula_hat;
    private Logger logger = new Logger();
    
    private static int my_auxiliary_index = 0;
    private Structure my_auxiliary_structure;
    
    // Constructors
    
    //@ assignable my_formula
    public Monitor(final String a_formula) {
        my_formula = new MFOTLFormula(a_formula);
    }
    
    // Public Methods
    
    /**
     * the main monitor algorithm
     * (MFOTL, Basin et al., page 10)
     */
    public void runMonitor(final TemporalStructure a_structure_sequence) {
        // i: current index in input sequence (D0, t0)...
        int q = 0; // index of next query evaluation in sequence (D0, t0) ...
        Q q_0 = new Q(my_formula.my_formula);
        
        
        //for (int i = 0; i < a_structure_sequence.my_structure.size(); i++) {
        for (int i = 0; i < 1; i++) {
            // carry over constants and relations of D_i to D'_i
            try {
                my_auxiliary_structure = (Structure) ((Structure) a_structure_sequence.my_structure.get(i)).clone();
            } catch(Exception exp) {
                logger.fatal(exp.getMessage());
            }

            /*
            my_auxiliary_structure = null;
            if (((Structure) a_structure_sequence.my_structure.get(i)) == null) {
                logger.fatal("Clone failed 000000000000000000000" + i);
            } else {
                logger.fatal("Clone succeed 11111111111111111111" + i);
            }*/
            
            formulaTransformation(a_structure_sequence, i);
            
            logger.debug("After Signature Extension & Formula Transformation");
            logger.debug(my_formula_hat.my_formula.toString());
            logger.debug(my_formula.my_formula.toString());
            logger.debug(my_formula_hat.toString());
            logger.debug(my_formula.toString());
            
            if (my_formula_hat.evaluation(my_auxiliary_structure)) {
                // TODO exit here, complete implementation
            }
        }
    }    

    // Private Methods
	private void signatureExtension() {
		/*
		 * R' = R Union {P_a|a temporal sub-formula of phi}
		 */
	    Set<TemporalFormula> temp_temporal_subformula = my_formula.my_temporal_subformula;
	    
	    for (TemporalFormula i : temp_temporal_subformula) {
	        /*
	         * Built new relation from temporal subformula (MFOTL, Basin et al., page 5)
	         */
	        logger.debug("Temporal Free Var: ");
	        logger.debug(i.getFreeVariable());
	        
	        createAuxiliaryPredicate(i);
	    }
	}
	
	//@ assignable my_formula_hat
	private void formulaTransformation(final TemporalStructure a_ts, final int a_pos) {
	    try {
	        my_formula_hat = (MFOTLFormula) my_formula.clone();
	    } catch (Exception cnse) {
	        logger.fatal(cnse.getMessage());
	    }
	    
	    /*
	    my_formula_hat.my_formula = null;
	    if (my_formula.my_formula == null) {
	        logger.fatal("000000000000000000000000");
	    } else {
	        logger.fatal("11111111111111111");
	    }*/
	    
	    if (my_formula_hat.my_formula.my_is_temporal) {
	        my_formula_hat = null;
	    } else {
	        transformTemporalSubformula(my_formula_hat.my_formula, a_ts, a_pos);
	    }
	}
	
	//@ assignable a_formula
	private void transformTemporalSubformula(final TemporalFormula a_formula, 
	        final TemporalStructure a_ts, final int a_pos) {
        if (a_formula == null) {
            return;
        }
        
        if ((a_formula.my_left_subformula != null) 
                && (a_formula.my_left_subformula.my_is_temporal)) {
            final Set<String> temp_var = ((TemporalFormula) a_formula.my_left_subformula).getFreeVariable();
            final String[] temp_var2 = new String[temp_var.size()];
            int j = 0;
            for (String i : temp_var) {
                temp_var2[j++] = i;
            }
            
            a_formula.my_left_subformula = new AtomicFormula(temp_var2, temp_var2.length, "p"+my_auxiliary_index);
            my_auxiliary_structure.initRelationAssign("p"+my_auxiliary_index++);
            
        } else if (a_formula.my_left_subformula instanceof TemporalFormula) {
            transformTemporalSubformula((TemporalFormula) a_formula.my_left_subformula, a_ts, a_pos);
        }
        
        if ((a_formula.my_right_subformula != null) 
                && (a_formula.my_right_subformula.my_is_temporal)) {
            final Set<String> temp_var = ((TemporalFormula) a_formula.my_right_subformula).getFreeVariable();
            final String[] temp_var2 = new String[temp_var.size()];
            int j = 0;
            for (String i : temp_var) {
                temp_var2[j++] = i;
            }
            
            a_formula.my_right_subformula = new AtomicFormula(temp_var2, temp_var2.length, "p"+my_auxiliary_index++);
            my_auxiliary_structure.initRelationAssign("p"+my_auxiliary_index++);
            
        } else if (a_formula.my_right_subformula instanceof TemporalFormula) {
            transformTemporalSubformula((TemporalFormula) a_formula.my_right_subformula, a_ts, a_pos);
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
	    Predicate temp_p_predicate = new Predicate("p", temp_free_var.size(), temp_freevar_array);
	    
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
