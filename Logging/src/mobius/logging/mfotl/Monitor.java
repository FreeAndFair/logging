package mobius.logging.mfotl;

import java.util.LinkedList;
import java.util.Set;

// TODO Implement the full algorithm

public class Monitor {
    // Attributes
    final private MFOTLFormula my_formula;
    final private Signature my_signature;
    final private TemporalStructure my_ats;
    final private Logger my_logger = new Logger();

    private static int my_auxiliary_index = 0;
    
    // Constructors
    //@ assignable my_signature;
    //@ assignable my_formula;
    //@ assignable my_ats;
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
        MFOTLFormula my_formula_hat;
        Structure my_auxiliary_structure;
        // i: current index in input sequence (D0, t0)...
        /*
        int q = 0; // index of next query evaluation in sequence (D0, t0) ...
        Q q_0 = new Q(my_formula.my_formula);
        */
        // Copy original structure for extension
        for (int i = 0; i < a_temporalstructure.getSize(); i++) {
            my_auxiliary_structure = new Structure ((Structure) a_temporalstructure.my_structure.get(i));
            my_ats.insertStructure(my_auxiliary_structure, a_temporalstructure.my_time_stamp.get(i));
        }
        
        // Formula Transformation
        my_logger.debug("Before Formula Transformation ----------" + my_formula.my_formula.toString());
        my_formula_hat = new MFOTLFormula(my_formula, my_signature);
        transformTemporalFormula(my_formula_hat.my_formula);
        my_logger.debug("After Formula Transformation ----------" + my_formula_hat.my_formula.toString());
        
        // Signature, Structure Extension & 
        my_logger.debug("Before Structure Extension ----------" + a_temporalstructure.toString());
        //extendStructure(my_formula_hat.my_formula);
        my_logger.debug("After Structure Extension ----------" + my_ats.toString());

        //for (int i = 0; i < my_ats.getSize(); i++) {
        for (int i = 0; i < 1; i++) {
            my_logger.debug("Start Evaluating Formula.........." + i);
            my_auxiliary_structure = my_ats.my_structure.get(i);
            my_logger.debug(my_auxiliary_structure.toString());
            if (my_formula_hat.evaluate(my_auxiliary_structure)){
                my_logger.debug("Evaluated to True for Structue No. " + i);
                // True returned, continue evaluating
            } else {
                my_logger.debug("Evaluated to False for Structure No. " + i);
                // False returned
            }
            my_logger.debug("End Evaluating Formula.........." + i);
        }
    }

    // Private Methods
	/**
	 * transform temporal formula 
	 * @param a_formula
	 */
    //@ assignable my_auxiliary_predicate;
    private void transformTemporalFormula(final /*@ non_null @*/ Formula a_formula) {
        if (a_formula == null || a_formula instanceof AtomicFormula) {
            return;
        }
	    
	    if (a_formula.my_is_temporal) {
	        transformTemporalFormula(((TemporalFormula) a_formula).my_left_subformula);
	        transformTemporalFormula(((TemporalFormula) a_formula).my_right_subformula);
	        
	        my_logger.debug("-------- ----------" + a_formula.toString());
	        
	        /**
	         * R' = R   Union {r_a|a temporal sub-formula of phi}
	         *          Union {p_a|a temporal sub-formula of the form S, U}
	         *          Union {s_a|a temporal sub-formula of the form U}
	         */
	        final LinkedList<String> temp_free_var = (LinkedList) ((TemporalFormula) a_formula).getFreeVariable();
	        final String[] temp_var = new String[temp_free_var.size()];
	        
	        // Introducing new predicate for all temporal predicate
	        int pos_j = 0;
	        for (String i: temp_free_var) {
	            temp_var[pos_j++] = i;
	        }
            String temp_formula_name = "p" + my_auxiliary_index;
            my_signature.addPredicate(new Predicate(temp_formula_name, temp_var.length));
            ((TemporalFormula) a_formula).my_auxiliary_predicate = new AtomicFormula(temp_var, temp_var.length, 
                    temp_formula_name, my_signature);
	        
            if (((TemporalFormula) a_formula).my_main_operator.my_name.equals("S")) {
                final String[] temp_var2 = new String[temp_var.length+1];
                System.arraycopy(temp_var, 0, temp_var2, 0, temp_var.length);
                temp_var2[temp_var.length] = "r0";
            
                temp_formula_name = "r" + my_auxiliary_index;
                my_signature.addPredicate(new Predicate(temp_formula_name, temp_var2.length));
                ((TemporalFormula) a_formula).my_auxiliary_predicate2 = new AtomicFormula(temp_var2, temp_var2.length, 
                        temp_formula_name, my_signature);
            }
            
            if (((TemporalFormula) a_formula).my_main_operator.my_name.equals("U")) {
                final String[] temp_var2 = new String[temp_var.length+1];
                System.arraycopy(temp_var, 0, temp_var2, 0, temp_var.length);
                temp_var2[temp_var.length] = "r0";
            
                temp_formula_name = "r" + my_auxiliary_index;
                my_signature.addPredicate(new Predicate(temp_formula_name, temp_var2.length));
                ((TemporalFormula) a_formula).my_auxiliary_predicate2 = new AtomicFormula(temp_var2, temp_var2.length, 
                        temp_formula_name, my_signature);
                
                final String[] temp_var3 = new String[temp_var.length+2];
                System.arraycopy(temp_var, 0, temp_var3, 0, temp_var.length);
                temp_var3[temp_var.length] = "s0";
                temp_var3[temp_var.length+1] = "s1";
                            
                temp_formula_name = "s" + my_auxiliary_index;
                my_signature.addPredicate(new Predicate(temp_formula_name, temp_var3.length));
                ((TemporalFormula) a_formula).my_auxiliary_predicate3 = new AtomicFormula(temp_var3, temp_var3.length, 
                        temp_formula_name, my_signature);
            }
            
            my_auxiliary_index ++;                
	    }
	}
	
	/**
	 * extend structure sequence
	 * @param a_formula
	 */
    //@ pure
	private void extendStructure(final Formula a_formula) {
	    if (a_formula == null) {
	        return;
	    }
	    
	    extendStructure(((TemporalFormula) a_formula).my_left_subformula);
	    extendStructure(((TemporalFormula) a_formula).my_right_subformula);
	    
        Structure my_auxiliary_structure;
        String temp_formula_name;
        int temp_time_interval;
        
        if (((TemporalFormula) a_formula).my_main_operator.my_name.equals("P")) {
            for (int a_pos = 1; a_pos < my_ats.getSize(); a_pos++) {
                my_auxiliary_structure = my_ats.my_structure.get(a_pos);
                temp_formula_name = ((TemporalFormula) a_formula).my_auxiliary_predicate.getName(); 
                my_auxiliary_structure.initRelationAssign(temp_formula_name);
                temp_time_interval = my_ats.my_time_stamp.get(a_pos) - my_ats.my_time_stamp.get(a_pos-1);
                
                if (((TemporalOperator)((TemporalFormula) a_formula).my_main_operator).inRange(temp_time_interval)) {
                    my_logger.debug("Security Policy NOT followed!");
                } else { // TODO BUG consider other cases
                    Set<int[]> temp_ra;
                    temp_ra = ((TemporalFormula) a_formula).my_right_subformula.evaluate(my_ats.my_structure.get(a_pos-1));
                    my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_ra);
                }
            }
        } else if (((TemporalFormula) a_formula).my_main_operator.my_name.equals("N")) {
            for (int a_pos = 0; a_pos < my_ats.getSize() - 1; a_pos++) {
                my_auxiliary_structure = my_ats.my_structure.get(a_pos);
                temp_formula_name = ((TemporalFormula) a_formula).my_auxiliary_predicate.getName();
                my_auxiliary_structure.initRelationAssign(temp_formula_name);
                temp_time_interval = my_ats.my_time_stamp.get(a_pos+1) - my_ats.my_time_stamp.get(a_pos);
                
                if (((TemporalOperator)((TemporalFormula) a_formula).my_main_operator).inRange(temp_time_interval)) {
                    my_logger.debug("Security Policy Not followed!");
                } else {
                    Set<int[]> temp_ra;
                    // TODO BUG replace with evaluation
                    temp_ra = my_ats.my_structure.get(a_pos+1).getRelationAssign(temp_formula_name);

                    my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_ra);
                }
            }
        } else if (((TemporalFormula) a_formula).my_main_operator.my_name.equals("S")) {
            for (int a_pos = 0; a_pos < my_ats.getSize(); a_pos++) {
                my_auxiliary_structure = my_ats.my_structure.get(a_pos);
                temp_formula_name = ((TemporalFormula) a_formula).my_auxiliary_predicate2.getName();
                my_auxiliary_structure.initRelationAssign(temp_formula_name);
                temp_time_interval = my_ats.my_time_stamp.get(a_pos+1) - my_ats.my_time_stamp.get(a_pos);
                // get r()
                
                
                // get p()
                Set<int[]> temp_ra = my_auxiliary_structure.getRelationAssign(temp_formula_name);
                temp_formula_name = ((TemporalFormula) a_formula).my_auxiliary_predicate.getName();
                for (int[] i : temp_ra) {
                    if (i[i.length-1] >= ((TemporalOperator)((TemporalFormula) a_formula).my_main_operator).getStart()) {
                        final int[] temp_j = new int[i.length-1];
                        System.arraycopy(i, 0, temp_j, 0, temp_j.length);
                        my_auxiliary_structure.addRelationAssign(temp_formula_name, i);
                    }
                }
            }
            // TODO add new predicate R
        } else if (((TemporalFormula) a_formula).my_main_operator.my_name.equals("U")) {
            for (int a_pos = 0; a_pos < my_ats.getSize(); a_pos++) {
                my_auxiliary_structure = my_ats.my_structure.get(a_pos);
                temp_formula_name = ((TemporalFormula) a_formula).my_auxiliary_predicate.getName();
                my_auxiliary_structure.initRelationAssign(temp_formula_name);
                temp_time_interval = my_ats.my_time_stamp.get(a_pos+1) - my_ats.my_time_stamp.get(a_pos);
                // get r()
                int loc = 0;
                
                // get s()
                
                // get p()
                Set<int[]> temp_ra = my_auxiliary_structure.getRelationAssign(temp_formula_name);
                temp_formula_name = ((TemporalFormula) a_formula).my_auxiliary_predicate.getName();
                for (int[] i : temp_ra) {
                    if (i[i.length-1] >= ((TemporalOperator)((TemporalFormula) a_formula).my_main_operator).getStart()) {
                        final int[] temp_j = new int[i.length-1];
                        System.arraycopy(i, 0, temp_j, 0, temp_j.length);
                        my_auxiliary_structure.addRelationAssign(temp_formula_name, i);
                    }
                }
            }
        }
    }
}


// TODO Rest part for optimization
	/*
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
	*/
	
	// internal class
	/**
	 * <p>
	 * <code>Q</code> is designed according to the paper, page 8
	 * </p>
	 */
	/*
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
}*/
