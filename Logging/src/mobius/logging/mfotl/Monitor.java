package mobius.logging.mfotl;

import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

public class Monitor {
    // Attributes
    final private MFOTLFormula my_formula;
    final private Signature my_signature;
    final private Logger my_logger = new Logger();
    
    private TemporalStructure my_ats;
    private static int my_auxiliary_index = 0;
    
    // Constructors
    //@ assignable my_signature;
    //@ assignable my_formula;
    public Monitor(final /*@ non_null @*/ String a_formula, final /*@ non_null @*/ Signature a_signature) {
        my_signature = a_signature;
        my_formula = new MFOTLFormula(a_formula, my_signature);
    }
    
    // Public Methods

    /**
     * The main monitoring algorithm
     * (MFOTL, Basin et al., page 10)
     * @param a_temporalstructure
     */
    public void runMonitor(final /*@ non_null @*/ TemporalStructure a_temporalstructure) {
        MFOTLFormula my_formula_hat;
        
        // Copy link of original structure for extension
        my_ats = a_temporalstructure;
        
        // Formula Transformation
        my_logger.debug("Before Formula Transformation ----------" + my_formula.getFormula().toString());
        my_formula_hat = new MFOTLFormula(my_formula, my_signature);
        transformTemporalFormula(my_formula_hat.getFormula());
        my_logger.debug("After Formula Transformation ----------" + my_formula_hat.getFormula().toString());
        
        // Signature, Structure Extension & 
        my_logger.debug("Before Structure Extension ----------" + a_temporalstructure.toString());
        extendStructure(my_formula_hat.getFormula());
        my_logger.debug("After Structure Extension ----------" + my_ats.toString());

        //for (int i = 0; i < my_ats.getSize(); i++) {
        for (int i = 0; i < 1; i++) {
            my_logger.debug("Start Evaluating Formula.........." + i);
            Structure my_auxiliary_structure = my_ats.getStructure(i);
            my_logger.debug(my_auxiliary_structure.toString());
            if (my_formula_hat.evaluateTruth(my_auxiliary_structure)){
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
	        transformTemporalFormula(((TemporalFormula) a_formula).getLeftSubformula());
	        transformTemporalFormula(((TemporalFormula) a_formula).getRightSubformula());
	        
	        my_logger.debug("-------- ----------" + a_formula.toString());
	        
	        /**
	         * R' = R   Union {r_a|a temporal sub-formula of phi}
	         *          Union {p_a|a temporal sub-formula of the form S, U}
	         *          Union {s_a|a temporal sub-formula of the form U}
	         */
	        final List<String> temp_free_var = (LinkedList) ((TemporalFormula) a_formula).getFreeVariable();
	        final String[] temp_var = new String[temp_free_var.size()];
	        
	        // Introducing new predicate for all temporal predicate
	        int pos_j = 0;
	        for (String i: temp_free_var) {
	            temp_var[pos_j++] = i;
	        }
            String temp_formula_name = "p" + my_auxiliary_index;
            my_signature.addPredicate(new Predicate(temp_formula_name, temp_var.length));
            ((TemporalFormula) a_formula).setAuxiliaryFormula(0, new AtomicFormula(temp_var, temp_var.length, 
                    temp_formula_name, my_signature));
	        
            if (((TemporalFormula) a_formula).getMainOperator().my_name.equals("S")) {
                final String[] temp_var2 = new String[temp_var.length+1];
                System.arraycopy(temp_var, 0, temp_var2, 0, temp_var.length);
                temp_var2[temp_var.length] = "r0";
            
                temp_formula_name = "r" + my_auxiliary_index;
                my_signature.addPredicate(new Predicate(temp_formula_name, temp_var2.length));
                ((TemporalFormula) a_formula).setAuxiliaryFormula(1, new AtomicFormula(temp_var2, temp_var2.length, 
                        temp_formula_name, my_signature));
            }
            
            if (((TemporalFormula) a_formula).getMainOperator().my_name.equals("U")) {
                final String[] temp_var2 = new String[temp_var.length+1];
                System.arraycopy(temp_var, 0, temp_var2, 0, temp_var.length);
                temp_var2[temp_var.length] = "r0";
            
                temp_formula_name = "r" + my_auxiliary_index;
                my_signature.addPredicate(new Predicate(temp_formula_name, temp_var2.length));
                ((TemporalFormula) a_formula).setAuxiliaryFormula(1, new AtomicFormula(temp_var2, temp_var2.length, 
                        temp_formula_name, my_signature));
                
                final String[] temp_var3 = new String[temp_var.length+2];
                System.arraycopy(temp_var, 0, temp_var3, 0, temp_var.length);
                temp_var3[temp_var.length] = "s0";
                temp_var3[temp_var.length+1] = "s1";
                            
                temp_formula_name = "s" + my_auxiliary_index;
                my_signature.addPredicate(new Predicate(temp_formula_name, temp_var3.length));
                ((TemporalFormula) a_formula).setAuxiliaryFormula(2, new AtomicFormula(temp_var3, temp_var3.length, 
                        temp_formula_name, my_signature));
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
	    if (a_formula == null || a_formula instanceof AtomicFormula) {
	        return;
	    }
	    
	    extendStructure(((TemporalFormula) a_formula).getLeftSubformula());
	    extendStructure(((TemporalFormula) a_formula).getRightSubformula());
	    
        Structure my_auxiliary_structure;
        String temp_formula_name;
        int temp_time_interval;
        
        if (((TemporalFormula) a_formula).getMainOperator().my_name.equals("P")) {
            for (int a_pos = 1; a_pos < my_ats.getSize(); a_pos++) {
                my_auxiliary_structure = my_ats.getStructure(a_pos);
                temp_formula_name = ((TemporalFormula) a_formula).getAuxiliaryFormula(0).getName(); 
                my_auxiliary_structure.initRelationAssign(temp_formula_name);
                temp_time_interval = my_ats.getTime(a_pos) - my_ats.getTime(a_pos-1);
                
                if (((TemporalOperator)((TemporalFormula) a_formula).getMainOperator()).inRange(temp_time_interval)) {
                    my_logger.debug("Security Policy NOT followed!");
                } else { // TODO BUG consider other cases
                    Set<int[]> temp_ra;
                    temp_ra = ((TemporalFormula) a_formula).getRightSubformula().evaluate(my_ats.getStructure(a_pos-1));
                    my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_ra);
                }
            }
        } else if (((TemporalFormula) a_formula).getMainOperator().my_name.equals("N")) {
            for (int a_pos = 0; a_pos < my_ats.getSize() - 1; a_pos++) {
                my_auxiliary_structure = my_ats.getStructure(a_pos);
                temp_formula_name = ((TemporalFormula) a_formula).getAuxiliaryFormula(0).getName();
                my_auxiliary_structure.initRelationAssign(temp_formula_name);
                temp_time_interval = my_ats.getTime(a_pos+1) - my_ats.getTime(a_pos);
                
                if (((TemporalOperator)((TemporalFormula) a_formula).getMainOperator()).inRange(temp_time_interval)) {
                    my_logger.debug("Security Policy Not followed!");
                } else {
                    // TODO BUG consider other cases
                    Set<int[]> temp_ra;
                    temp_ra = ((TemporalFormula) a_formula).getRightSubformula().evaluate(my_ats.getStructure(a_pos-1));
                    my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_ra);
                }
            }
        } else if (((TemporalFormula) a_formula).getMainOperator().my_name.equals("S")) {
            for (int a_pos = 0; a_pos < my_ats.getSize(); a_pos++) {
                my_auxiliary_structure = my_ats.getStructure(a_pos);
                temp_formula_name = ((TemporalFormula) a_formula).getAuxiliaryFormula(1).getName();
                my_auxiliary_structure.initRelationAssign(temp_formula_name);
                temp_time_interval = my_ats.getTime(a_pos+1) - my_ats.getTime(a_pos);
                // get r()
                
                // gama ^ Di * {0}
                final Set<int[]> gama = ((TemporalFormula) a_formula).getRightSubformula().evaluate(my_auxiliary_structure);
                for (int[] i : gama) {
                    int[] temp_gama = new int[i.length+1];
                    System.arraycopy(i, 0, temp_gama, 0, i.length);
                    temp_gama[i.length] = 0;
                    my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_gama);
                }
                // beta part
                if (a_pos > 0) {
                    final Set<int[]> beta = ((TemporalFormula) a_formula).getLeftSubformula().evaluate(my_auxiliary_structure);
                    final Set<int[]> beta2 = my_ats.getStructure(a_pos-1).getRelationAssign(temp_formula_name);
                    final int time_beta = my_ats.getTime(a_pos);
                    final int time_beta2 = my_ats.getTime(a_pos-1);
                    for (int[] i : beta2) {
                        int[] temp_gama2 = new int[i.length-1];
                        System.arraycopy(i, 0, temp_gama2, 0, temp_gama2.length);
                        if (beta.contains(temp_gama2)) {
                            int[] temp_gama = new int[i.length];
                            System.arraycopy(i, 0, temp_gama2, 0, i.length);
                            temp_gama[i.length-1] += time_beta - time_beta2;
                            my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_gama);
                        }
                    }
                }
                
                // get p()
                Set<int[]> temp_ra = my_auxiliary_structure.getRelationAssign(temp_formula_name);
                temp_formula_name = ((TemporalFormula) a_formula).getAuxiliaryFormula(0).getName();
                for (int[] i : temp_ra) {
                    if (i[i.length-1] >= ((TemporalOperator)((TemporalFormula) a_formula).getMainOperator()).getStart()) {
                        final int[] temp_j = new int[i.length-1];
                        System.arraycopy(i, 0, temp_j, 0, temp_j.length);
                        my_auxiliary_structure.addRelationAssign(temp_formula_name, i);
                    }
                }
            }
        } else if (((TemporalFormula) a_formula).getMainOperator().my_name.equals("U")) {
            int[] loc = new int[my_ats.getSize()];
            final int interval_start = ((TemporalOperator)((TemporalFormula) a_formula).getMainOperator()).getStart();
            final int interval_end = ((TemporalOperator)((TemporalFormula) a_formula).getMainOperator()).getEnd();
            for (int a_pos = 0; a_pos < my_ats.getSize(); a_pos++) {
                my_auxiliary_structure = my_ats.getStructure(a_pos);
                temp_formula_name = ((TemporalFormula) a_formula).getAuxiliaryFormula(1).getName();
                my_auxiliary_structure.initRelationAssign(temp_formula_name);
                temp_time_interval = my_ats.getTime(a_pos+1) - my_ats.getTime(a_pos);
                // get r()

                
                // compute l_i, a lookahead offset
                for (int i = a_pos; i< my_ats.getSize(); i++) {
                    if (my_ats.getTime(i) - my_ats.getTime(a_pos) < interval_end) {
                        loc[a_pos] = i;
                    } else {
                        break;
                    }
                }

                // get r() := new_r Union update_r
                if (a_pos == 0) {
                    // new_r
                    for (int i = 0; i < loc[a_pos]; i++) {
                        if ((my_ats.getTime(i + a_pos) - my_ats.getTime(a_pos)) >= interval_start) { 
                            Set<int[]> temp_r = ((TemporalFormula) a_formula).getRightSubformula().evaluate(my_ats.getStructure(i+a_pos));
                            for (int[] j : temp_r) {
                                int[] temp_j = new int[j.length + 1];
                                System.arraycopy(j, 0, temp_j, 0, j.length);
                                temp_j[j.length] = i;
                                my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_j);
                            }
                        }
                    }
                    
                    // update_r empty
                } else {
                    // new_r
                    for (int i = loc[a_pos-1]; i < loc[a_pos]; i++) {
                        if ((my_ats.getTime(i + a_pos) - my_ats.getTime(a_pos)) >= interval_start) { 
                            Set<int[]> temp_r = ((TemporalFormula) a_formula).getRightSubformula().evaluate(my_ats.getStructure(i+a_pos));
                            for (int[] j : temp_r) {
                                int[] temp_j = new int[j.length + 1];
                                System.arraycopy(j, 0, temp_j, 0, j.length);
                                temp_j[j.length] = i;
                                my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_j);
                            }
                        }
                    }
                    
                    // update_r
                    final Set<int[]> temp_r = my_ats.getStructure(a_pos-1).getRelationAssign(temp_formula_name);
                    for (int[] i : temp_r) {
                        if (i[i.length-1] > 0) {
                            i[i.length-1] --;
                            if ((my_ats.getTime(i[i.length-1]+a_pos) - my_ats.getTime(a_pos)) >= interval_start) {
                                my_auxiliary_structure.addRelationAssign(temp_formula_name, i);
                            }
                        }
                    }
                }
                
                // get s() := new_s Union update_s
                int pos_j, pos_j2;
                Set<int[]> new_s = new HashSet();
                Set<int[]> update_s = new HashSet();
                temp_formula_name = ((TemporalFormula) a_formula).getAuxiliaryFormula(2).getName();
                if (a_pos == 0) {
                    // new_s
                    pos_j = 0;
                    pos_j2 = loc[a_pos];
                    
                    for (int i = pos_j; i <= pos_j2; i++) {
                        Set<int[]> temp_r = ((TemporalFormula) a_formula).getLeftSubformula().evaluate(my_ats.getStructure(i));
                        for (int j= pos_j2; j >= i; j--) {
                            Set<int[]> temp_r2 = ((TemporalFormula) a_formula).getLeftSubformula().evaluate(my_ats.getStructure(j));
                            temp_r.retainAll(temp_r2);
                        }
                        if (!temp_r.isEmpty()) {
                            for (int[] a_i : temp_r){
                                int[] a_temp = new int[a_i.length+2];
                                System.arraycopy(a_i, 0, a_temp, 0, a_i.length);
                                a_temp[a_i.length] = i;
                                a_temp[a_i.length+1] = pos_j2;
                                new_s.add(a_temp);
                            }
                        } else {
                            pos_j2--;
                        }
                    }
                    
                    // update_s = EMPTY
                } else {
                    // new_s
                    pos_j = loc[a_pos-1];
                    pos_j2 = loc[a_pos];
                    
                    for (int i = pos_j; i <= pos_j2; i++) {
                        Set<int[]> temp_r = ((TemporalFormula) a_formula).getLeftSubformula().evaluate(my_ats.getStructure(i));
                        for (int j= pos_j2; j >= i; j--) {
                            Set<int[]> temp_r2 = ((TemporalFormula) a_formula).getLeftSubformula().evaluate(my_ats.getStructure(j));
                            temp_r.retainAll(temp_r2);
                        }
                        if (!temp_r.isEmpty()) {
                            for (int[] a_i : temp_r){
                                int[] a_temp = new int[a_i.length+2];
                                System.arraycopy(a_i, 0, a_temp, 0, a_i.length);
                                a_temp[a_i.length] = i;
                                a_temp[a_i.length+1] = pos_j2;
                                new_s.add(a_temp);
                            }
                        } else {
                            pos_j2--;
                        }
                    }
                    
                    // update_s
                    Set<int[]> set_temp = my_ats.getStructure(a_pos-1).getRelationAssign(temp_formula_name);
                    for (int[] a_i : set_temp) {
                        if (a_i[a_i.length-1] > 0 && a_i[a_i.length-2] > 0) {
                            a_i[a_i.length-1]--;
                            a_i[a_i.length-2]--;
                            update_s.add(a_i);
                        }
                        if (a_i[a_i.length-1] == loc[a_pos-1]) {
                            //TODO check arrary range
                            pos_j = a_i[a_i.length-2] - 1;
                            int[] a_temp = new int[a_i.length-1];
                            System.arraycopy(a_i, 0, a_temp, 0, a_temp.length);
                            a_temp[a_temp.length-1] = a_i[a_i.length-1];
                            for (int[] a_j : new_s) {
                                int[] a_temp2 = new int[a_j.length-1];
                                System.arraycopy(a_j, 0, a_temp2, 0, a_temp2.length);
                                if (Arrays.equals(a_temp, a_temp2)) {
                                    int[] a_temp3 = new int[a_i.length];
                                    System.arraycopy(a_i, 0, a_temp3, 0, a_temp3.length);
                                    a_temp3[a_temp3.length-2] = pos_j;
                                    a_temp3[a_temp3.length-1] = a_j[a_j.length-1];
                                    update_s.add(a_temp3);
                                }
                            }
                        }
                    }
                }
                
                // get p()
                Set<int[]> temp_sa = my_auxiliary_structure.getRelationAssign(temp_formula_name);
                temp_formula_name = ((TemporalFormula) a_formula).getAuxiliaryFormula(2).getName();
                Set<int[]> temp_ra = my_auxiliary_structure.getRelationAssign(temp_formula_name);
                
                temp_formula_name = ((TemporalFormula) a_formula).getAuxiliaryFormula(0).getName();
                for (int[] a_i : temp_ra) {
                    pos_j = a_i[a_i.length-1];
                    final int[] a_temp = new int[a_i.length-1];
                    System.arraycopy(a_i, 0, a_temp, 0, a_temp.length);
                    for (int[] a_j : temp_sa) {
                        pos_j2 = a_j[a_j.length-1];
                        if ((a_j[a_j.length-2] == 0) && (pos_j <= pos_j2+1)) {
                            final int[] a_temp2 = new int[a_j.length -2];
                            System.arraycopy(a_j, 0, a_temp2, 0, a_temp2.length);
                            if (Arrays.equals(a_temp, a_temp2)) {
                                my_auxiliary_structure.addRelationAssign(temp_formula_name, a_temp);        
                            }
                        }
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
