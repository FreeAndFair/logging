package demtech.mfotl;

import java.util.Arrays;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

public class Monitor {
    // Attributes
    private static int my_auxiliary_index = 0;
    final private Signature my_signature;
    final private MFOTLFormula my_formula_hat;
    final private Logger my_logger = new Logger();
    
    // Constructors
    //@ assignable my_signature;
    //@ assignable my_formula;
    public Monitor(final String a_formula, final Signature a_signature) {
        my_signature = a_signature;
        my_formula_hat = new MFOTLFormula(a_formula, my_signature);
    }
    
    // Public Methods
    /**
     * The main monitoring algorithm
     * (MFOTL, Basin et al., page 10)
     * @param a_temporalstructure
     */
    public void runMonitor(final TemporalStructure my_ats) {
        // Formula Transformation
        my_logger.debug("Before Formula Transformation ---------------------\n" + my_formula_hat.getFormula().toString());
        transformTemporalFormula(my_formula_hat.getFormula());
        my_logger.debug("After Formula Transformation ---------------------\n" + my_formula_hat.getFormula().toString());
        
        // Signature and Structure Extension 
        my_logger.debug("Before Structure Extension ---------------------\n" + my_ats.toString());
        extendStructure(my_formula_hat.getFormula(), my_ats);
        my_logger.debug("After Structure Extension ---------------------\n" + my_ats.toString());

        for (int i = 0; i < my_ats.getSize(); i++) {
            my_logger.debug("Start Evaluating Formula.........." + i);
            final Structure my_auxiliary_structure = my_ats.getStructure(i);
            my_logger.debug(my_auxiliary_structure.toString());
            if (my_formula_hat.evaluateTruth(my_auxiliary_structure)){
                my_logger.debug("Evaluated to True for Structue No. " + i + "TTTTTTTTTTTTTTTTTTTTTTTTTT");
                // True returned, continue evaluating
            } else {
                my_logger.warning("Evaluated to False for Structure No. " + i + "FFFFFFFFFFFFFFFFFFFFFFFFFF");
                // False returned, continue evaluating
            }
            my_logger.debug("End Evaluating Formula.........." + i + "\n");
        }
    }
    
    // Private Methods
    /*
     * this is used only applied once before the monitoring 
     */
    //@ assignable my_auxiliary_predicate;
    private void transformTemporalFormula(final Formula a_formula) {
        if (a_formula == null || a_formula instanceof AtomicFormula) {
            return;
        }

        transformTemporalFormula(((TemporalFormula) a_formula).getLeftSubformula());
        transformTemporalFormula(((TemporalFormula) a_formula).getRightSubformula());
	    
	    if (a_formula.my_is_temporal) {
	        my_logger.debug("-------- ----------" + a_formula.toString());
	        
	        final List<String> temp_free_var = (LinkedList) ((TemporalFormula) a_formula).getFreeVariable();
	        final String[] temp_var = new String[temp_free_var.size()];
	        
	        // Introducing new predicate for all temporal predicate
	        int pos_j = 0;
	        for (String i: temp_free_var) {
	            temp_var[pos_j++] = i;
	        }

	        String temp_formula_name = "p" + my_auxiliary_index;
            my_signature.addPredicate(new Predicate(temp_formula_name, temp_var.length));
            ((TemporalFormula) a_formula).setAuxiliaryFormula(0, new AtomicFormula(temp_var, 
                    temp_formula_name, my_signature));
	        
            if (((TemporalFormula) a_formula).getMainOperator().my_name.equals("S")) {
                final String[] temp_var2 = new String[temp_var.length+1];
                System.arraycopy(temp_var, 0, temp_var2, 0, temp_var.length);
                temp_var2[temp_var.length] = "r0";
            
                temp_formula_name = "r" + my_auxiliary_index;
                my_signature.addPredicate(new Predicate(temp_formula_name, temp_var2.length));
                ((TemporalFormula) a_formula).setAuxiliaryFormula(1, new AtomicFormula(temp_var2, 
                        temp_formula_name, my_signature));
            }
            
            if (((TemporalFormula) a_formula).getMainOperator().my_name.equals("U")) {
                final String[] temp_var2 = new String[temp_var.length+1];
                System.arraycopy(temp_var, 0, temp_var2, 0, temp_var.length);
                temp_var2[temp_var.length] = "r0";
            
                temp_formula_name = "r" + my_auxiliary_index;
                my_signature.addPredicate(new Predicate(temp_formula_name, temp_var2.length));
                ((TemporalFormula) a_formula).setAuxiliaryFormula(1, new AtomicFormula(temp_var2, 
                        temp_formula_name, my_signature));
                
                final String[] temp_var3 = new String[temp_var.length+2];
                System.arraycopy(temp_var, 0, temp_var3, 0, temp_var.length);
                temp_var3[temp_var.length] = "s0";
                temp_var3[temp_var.length+1] = "s1";
                
                temp_formula_name = "s" + my_auxiliary_index;
                my_signature.addPredicate(new Predicate(temp_formula_name, temp_var3.length));
                ((TemporalFormula) a_formula).setAuxiliaryFormula(2, new AtomicFormula(temp_var3, 
                        temp_formula_name, my_signature));
            }
            
            my_auxiliary_index ++;
	    }
	}
	
    //@ pure
	private void extendStructure(final Formula a_formula, final TemporalStructure my_ats) {
	    if (a_formula == null || a_formula instanceof AtomicFormula) {
	        return;
	    } 
	    
	    extendStructure(((TemporalFormula) a_formula).getLeftSubformula(), my_ats);
	    extendStructure(((TemporalFormula) a_formula).getRightSubformula(), my_ats);

	    if (((TemporalFormula) a_formula).getMainOperator() == null) { 
            return;
        }
	    
        if (((TemporalFormula) a_formula).getMainOperator().my_name.equals("P")) {
            extendP((TemporalFormula) a_formula, my_ats);
        } else if (((TemporalFormula) a_formula).getMainOperator().my_name.equals("N")) {
            extendN((TemporalFormula) a_formula, my_ats);
        } else if (((TemporalFormula) a_formula).getMainOperator().my_name.equals("S")) {
            extendS((TemporalFormula) a_formula, my_ats);
        } else if (((TemporalFormula) a_formula).getMainOperator().my_name.equals("U")) {
            extendU((TemporalFormula) a_formula, my_ats);

        }
    }

	private void extendP(final TemporalFormula a_formula, final TemporalStructure my_ats) {
        for (int a_pos = 1; a_pos < my_ats.getSize(); a_pos++) {
            final Structure my_auxiliary_structure = my_ats.getStructure(a_pos);
            final String temp_formula_name = ((TemporalFormula) a_formula).getAuxiliaryFormula(0).getName(); 
            final int temp_time_interval = my_ats.getTime(a_pos) - my_ats.getTime(a_pos-1);
            
            if (((TemporalOperator)((TemporalFormula) a_formula).getMainOperator()).inRange(temp_time_interval)) {
                final Evaluation temp_ra = ((TemporalFormula) a_formula).getRightSubformula().evaluate(my_ats.getStructure(a_pos-1));
                if (temp_ra.isTrue()) {
                    my_auxiliary_structure.addNullaryRelation(temp_formula_name);
                } else {
                    my_auxiliary_structure.initRelationAssign(temp_formula_name);
                    my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_ra.getSet());
                }
            } else {
                my_logger.warning("Security Policy NOT followed! ------- Time Interval: " + temp_time_interval);    
            }
        }
	}
	
    private void extendN(final TemporalFormula a_formula, final TemporalStructure my_ats) {
        for (int a_pos = 0; a_pos < my_ats.getSize() - 1; a_pos++) {
            final Structure my_auxiliary_structure = my_ats.getStructure(a_pos);
            final String temp_formula_name = ((TemporalFormula) a_formula).getAuxiliaryFormula(0).getName();
            final int temp_time_interval = my_ats.getTime(a_pos+1) - my_ats.getTime(a_pos);
            
            if (((TemporalOperator)((TemporalFormula) a_formula).getMainOperator()).inRange(temp_time_interval)) {
                final Evaluation temp_ra = ((TemporalFormula) a_formula).getRightSubformula().evaluate(my_ats.getStructure(a_pos+1));
                if (temp_ra.isTrue()) {
                    my_auxiliary_structure.addNullaryRelation(temp_formula_name);
                } else {
                    my_auxiliary_structure.initRelationAssign(temp_formula_name);
                    my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_ra.getSet());
                }
            } else {
                my_logger.warning("Security Policy Not followed! ------- Time Interval: " + temp_time_interval);
            }
        }
	}
    
    private void extendS(final TemporalFormula a_formula, final TemporalStructure my_ats) {
        for (int a_pos = 0; a_pos < my_ats.getSize(); a_pos++) {
            final String temp_formula_name0 = ((TemporalFormula) a_formula).getAuxiliaryFormula(0).getName();
            final String temp_formula_name = ((TemporalFormula) a_formula).getAuxiliaryFormula(1).getName();
            
            final Structure my_auxiliary_structure = my_ats.getStructure(a_pos);
            my_auxiliary_structure.initRelationAssign(temp_formula_name);
            
            // gama ^ Di * {0}, get r()
            final Evaluation gama0 = ((TemporalFormula) a_formula).getRightSubformula().evaluate(my_auxiliary_structure);
            if (gama0.isTrue()) {
                my_logger.warning("!!!!!!!!!!!!!!!!!!!!Here1?????????????????????\n");
                int[] temp_gama = new int[1];
                temp_gama[0] = 0;
                my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_gama);
            } else {
                for (int[] i : gama0.getSet()) {
                    int[] temp_gama = new int[i.length+1];
                    System.arraycopy(i, 0, temp_gama, 0, i.length);
                    temp_gama[i.length] = 0;
                    my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_gama);
                }
            }
            
            if (a_pos > 0) {
                final int temp_time_interval = my_ats.getTime(a_pos) - my_ats.getTime(a_pos-1);

                // beta part
                final Evaluation beta_eval = ((TemporalFormula) a_formula).getLeftSubformula().evaluate(my_auxiliary_structure);
                final Set<int[]> beta = beta_eval.getSet();
                final Set<int[]> beta2 = my_ats.getStructure(a_pos-1).getRelationAssign(temp_formula_name);
                
                if (beta2 == null) {
                    continue;
                } else {
                    for (int[] i : beta2) {
                        System.err.print("!!!!!!!!!!!!!!!!!!!!Here3.3\n");
                        final int[] temp_gama2 = new int[i.length-1];
                        System.arraycopy(i, 0, temp_gama2, 0, temp_gama2.length);
                        if (beta_eval.isTrue() || beta.contains(temp_gama2)) {
                            int[] temp_gama = new int[i.length];
                            System.arraycopy(i, 0, temp_gama, 0, i.length);
                            temp_gama[i.length-1] += temp_time_interval;
                            my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_gama);
                        }
                    }
                }
            }
            
            // get p()
            final Set<int[]> temp_ra = my_auxiliary_structure.getRelationAssign(temp_formula_name);

            for (int[] i : temp_ra) {
                if (i[i.length-1] >= ((TemporalOperator)((TemporalFormula) a_formula).getMainOperator()).getStart()) {
                    System.err.print("!!!!!!!!!!!!!!!!!!!!Here4.5\n");
                    if (i.length == 1) {
                        my_auxiliary_structure.addNullaryRelation(temp_formula_name0);
                    } else {
                        final int[] temp_j = new int[i.length-1];
                        System.arraycopy(i, 0, temp_j, 0, temp_j.length);
                        my_auxiliary_structure.initRelationAssign(temp_formula_name0);
                        my_auxiliary_structure.addRelationAssign(temp_formula_name0, i);
                    }
                }
            }
        }
    }
    
    private void extendU(final TemporalFormula a_formula, final TemporalStructure my_ats) {
        final int[] lookahead_offset = new int[my_ats.getSize()];
        final int interval_start = ((TemporalOperator)a_formula.getMainOperator()).getStart();
        final int interval_end = ((TemporalOperator)a_formula.getMainOperator()).getEnd();
        
        final Structure[] temp_structure = new Structure[my_ats.getSize()];
        String temp_formula_name = a_formula.getAuxiliaryFormula(2).getName();
        for (int i = 0; i < my_ats.getSize(); i++) {
            temp_structure[i] = new Structure();

            final Structure my_auxiliary_structure = my_ats.getStructure(i);
            final Evaluation temp_ev = a_formula.getLeftSubformula().evaluate(my_auxiliary_structure);
            if (temp_ev.isTrue()) {
                temp_structure[i].addNullaryRelation(temp_formula_name);
            } else {
                final Set<int[]> temp_r = temp_ev.getSet();
                if (!temp_r.isEmpty()) {
                    temp_structure[i].initRelationAssign(temp_formula_name);                    
                    temp_structure[i].addRelationAssign(temp_formula_name, temp_r);
                }
            }
            my_logger.warning(" " + i + "::" + temp_structure[i].toString());
        }
        
        for (int a_pos = 0; a_pos < my_ats.getSize(); a_pos++) {
            final Structure my_auxiliary_structure = my_ats.getStructure(a_pos);
            temp_formula_name = a_formula.getAuxiliaryFormula(1).getName();
            my_auxiliary_structure.initRelationAssign(temp_formula_name);
            //int temp_time_interval = my_ats.getTime(a_pos+1) - my_ats.getTime(a_pos);
            // get r()
            
            // compute l_i, the lookahead offset
            for (int i = a_pos; i < my_ats.getSize(); i++) {
                if (my_ats.getTime(i) - my_ats.getTime(a_pos) < interval_end) {
                    lookahead_offset[a_pos] = i - a_pos;
                } else {
                    break;
                }
            }
            
            if (a_pos == my_ats.getSize()-1) {
                for (int i = 0; i <= a_pos; i++) {
                    my_logger.warning("" + lookahead_offset[i]);
                }
            }

            // get r() := new_r Union update_r
            if (a_pos == 0) {
                // new_r
                for (int i = 0; i <= lookahead_offset[a_pos]; i++) { // l_i-1 <= j <= l_i, where i=0, l_-1 = 0
                    if ((my_ats.getTime(i + a_pos) - my_ats.getTime(a_pos)) >= interval_start) { // t_i+j - t_i >= c
                        final Evaluation temp_ev = a_formula.getRightSubformula().evaluate(my_ats.getStructure(i+a_pos));
                        if (temp_ev.isTrue()) {
                            int[] temp_array = new int[1];
                            temp_array[0] = i;
                            my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_array);
                        } else {
                            final Set<int[]> temp_r = temp_ev.getSet();
                            for (int[] j : temp_r) {
                                int[] temp_j = new int[j.length + 1];
                                System.arraycopy(j, 0, temp_j, 0, j.length);
                                temp_j[j.length] = i;
                                my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_j);
                            }
                        }
                    }
                }
                
                // update_r = Empty
            } else {
                // new_r
                for (int i = lookahead_offset[a_pos-1]; i <= lookahead_offset[a_pos]; i++) { // l_i-1 <= j <= l_i, where i = pos
                    if ((my_ats.getTime(i + a_pos) - my_ats.getTime(a_pos)) >= interval_start) {
                        final Evaluation temp_ev = a_formula.getRightSubformula().evaluate(my_ats.getStructure(i+a_pos));
                        if (temp_ev.isTrue()) {
                            int[] temp_array = new int[1];
                            temp_array[0] = i;
                            my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_array);
                        } else {
                            final Set<int[]> temp_r2 = temp_ev.getSet();
                            for (int[] j : temp_r2) {
                                int[] temp_j = new int[j.length + 1];
                                System.arraycopy(j, 0, temp_j, 0, j.length);
                                temp_j[j.length] = i;
                                my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_j);
                            }
                        }
                    }
                }
                
                // update_r
                final Set<int[]> temp_r = my_ats.getStructure(a_pos-1).getRelationAssign(temp_formula_name);
                for (int[] i : temp_r) {
                    int[] copy_i = new int[i.length];
                    System.arraycopy(i, 0, copy_i, 0, i.length);
                    copy_i[i.length-1] = i[i.length-1] - 1;
                    if (copy_i[i.length-1] < 0) {
                        continue;
                    }
                    if ((my_ats.getTime(copy_i[i.length-1]+a_pos) - my_ats.getTime(a_pos)) >= interval_start) {
                        my_auxiliary_structure.addRelationAssign(temp_formula_name, copy_i);
                    }
                }
            }
            
            // get s() := new_s Union update_s
            int pos_j, pos_j2;
            final Set<int[]> new_s = new HashSet();
            final Set<int[]> update_s = new HashSet();
            temp_formula_name = a_formula.getAuxiliaryFormula(2).getName();
            my_auxiliary_structure.initRelationAssign(temp_formula_name);
            if (a_pos == 0) {
                // new_s
                pos_j = 0;
                pos_j2 = lookahead_offset[a_pos];
                
                for (int i = pos_j; i <= pos_j2; i++) {
                    if (temp_structure[i].containsNullaryRelation(temp_formula_name)) {
                        int[] a_temp = new int[2];
                        a_temp[0] = i;
                        a_temp[1] = i;
                        for (int j = i + 1;  j <= pos_j2; j++) {
                            if (temp_structure[j].containsNullaryRelation(temp_formula_name)) {
                                a_temp[1] = j;
                            }
                        }
                        new_s.add(a_temp);
                        my_auxiliary_structure.addRelationAssign(temp_formula_name, a_temp);
                    }
                }
                
                
                /*
                for (int i = pos_j; i <= pos_j2; i++) {
                    final Evaluation temp_ev = a_formula.getLeftSubformula().evaluate(my_ats.getStructure(i));
                    final Set<int[]> temp_r = temp_ev.getSet();
                    for (int j = pos_j2; j >= i; j--) {
                        final Evaluation temp_ev2 = a_formula.getLeftSubformula().evaluate(my_ats.getStructure(j));
                        if (temp_ev2.isTrue()) {
                            
                        }
                        
                        final Set<int[]> temp_r2 = temp_ev2.getSet();
                        retainAll(temp_r, temp_r2);
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
                }*/
                
                // update_s = EMPTY
            } else {
                // new_s
                pos_j = lookahead_offset[a_pos-1];
                pos_j2 = lookahead_offset[a_pos];
                
                for (int i = pos_j; i <= pos_j2; i++) {
                    if (temp_structure[a_pos + i].containsNullaryRelation(temp_formula_name)) {
                        int[] a_temp = new int[2];
                        a_temp[0] = i;
                        a_temp[1] = i;
                        for (int j = i + 1;  j <= pos_j2; j++) {
                            if (temp_structure[a_pos + j].containsNullaryRelation(temp_formula_name)) {
                                a_temp[1] = j;
                            }
                        }
                        new_s.add(a_temp);
                        my_auxiliary_structure.addRelationAssign(temp_formula_name, a_temp);
                    }
                }
                
                /*
                for (int i = pos_j; i <= pos_j2; i++) {
                    Set<int[]> temp_r = ((TemporalFormula) a_formula).getLeftSubformula().evaluate(my_ats.getStructure(i)).getSet();
                    for (int j= pos_j2; j >= i; j--) {
                        Set<int[]> temp_r2 = ((TemporalFormula) a_formula).getLeftSubformula().evaluate(my_ats.getStructure(j)).getSet();
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
                }*/
                
                // update_s
                final Set<int[]> set_temp = my_ats.getStructure(a_pos-1).getRelationAssign(temp_formula_name);
                for (int[] a_i : set_temp) {
                    // U_s part one, page 8
                    int[] temp_array = new int[a_i.length];
                    System.arraycopy(a_i, 0, temp_array, 0, a_i.length);
                    if (a_i[a_i.length-1] > 0 && a_i[a_i.length-2] > 0) {
                        temp_array[a_i.length-1]--;
                        temp_array[a_i.length-2]--;
                        update_s.add(temp_array);
                        my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_array);
                    }
                    
                    // U_s part two, page 8
                    if (a_i[a_i.length-1] == lookahead_offset[a_pos-1]) {
                        pos_j = a_i[a_i.length-2] - 1;
                        int[] a_temp = new int[a_i.length-1];
                        System.arraycopy(a_i, 0, a_temp, 0, a_temp.length);
                        a_temp[a_temp.length-1] = a_i[a_i.length-1];
                        for (int[] a_j : new_s) {
                            final int[] a_temp2 = new int[a_j.length-1];
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
            temp_formula_name = a_formula.getAuxiliaryFormula(2).getName();
            final Set<int[]> temp_sa = my_auxiliary_structure.getRelationAssign(temp_formula_name);
            temp_formula_name = a_formula.getAuxiliaryFormula(1).getName();
            final Set<int[]> temp_ra = my_auxiliary_structure.getRelationAssign(temp_formula_name);
            temp_formula_name = a_formula.getAuxiliaryFormula(0).getName();
            
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
                            if (a_temp.length > 0) {
                                my_auxiliary_structure.initRelationAssign(temp_formula_name);
                                my_auxiliary_structure.addRelationAssign(temp_formula_name, a_temp);
                            } else {
                                my_auxiliary_structure.addNullaryRelation(temp_formula_name);
                            }
                        }
                    }
                }
            }
        }
    }
}