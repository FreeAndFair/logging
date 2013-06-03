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
    final private MFOTLFormula my_formula;
    final private TemporalStructure my_ats2;
    
    final private Logger my_logger = new Logger();
    
    // Constructors
    //@ assignable my_signature;
    //@ assignable my_formula;
    public Monitor(final String a_formula, final Signature a_signature) {
        my_signature = a_signature;
        my_formula = new MFOTLFormula(a_formula, my_signature);
        my_ats2 = new TemporalStructure();
        
        this.preProcess();
    }
    
    // Public Methods
    /**
     * The main monitoring algorithm
     * (MFOTL, Basin et al., page 10)
     * @param a_temporalstructure
     */
    /*
    public void runMonitor(final TemporalStructure a_ts) {
        // Signature and Structure Extension
        my_logger.debug("Before Structure Extension ---------------------\n" + a_ts.toString());
        extendStructure(my_formula.getFormula(), a_ts);
        my_logger.debug("After Structure Extension ---------------------\n" + a_ts.toString());

        for (int i = 0; i < a_ts.getSize(); i++) {
            my_logger.debug("Start Evaluating Formula.........." + i);
            final Structure my_auxiliary_structure = a_ts.getStructure(i);
            my_logger.debug(my_auxiliary_structure.toString());
            if (my_formula.evaluateTruth(my_auxiliary_structure)){
                my_logger.warning("Evaluated to True for Structue No. " + i + "TTTTTTTTTTTTTTTTTTTTTTTTTT");
                // True returned, continue evaluating
            } else {
                my_logger.warning("Evaluated to False for Structure No. " + i + "FFFFFFFFFFFFFFFFFFFFFFFFFF");
                // False returned, continue evaluating
            }
            my_logger.debug("End Evaluating Formula.........." + i + "\n");
        }
    }*/
    
    public void addStructure(final Structure a_structure, final int a_time_stamp) {
        my_ats2.insertStructure(a_structure, a_time_stamp);
        final int temp_pos = my_ats2.getSize() - 1;
        final int temp_es = extendStructure(my_formula.getFormula(), temp_pos);
        
        my_logger.debug("Start evaluate with ... No. " + temp_pos + " ... Structure : " + temp_es);
        
        if (temp_es < 0) {
            my_logger.warning("Unable to evaluate Formula with ... No. " + temp_pos + " ... Structure");
        } else {
            final Structure my_auxiliary_structure = my_ats2.getStructure(temp_es);
            my_logger.debug("Extended Structure: " + my_auxiliary_structure.toString());
            
            my_logger.warning("Evaluating with Structure No. " + temp_es);
            if (my_formula.evaluateTruth(my_auxiliary_structure)){
                my_logger.warning("Evaluated No. " + temp_es +  " to True " + "TTTTTTTTTTTTTTTTTTTTTTTTTT");
            } else {
                my_logger.warning("Evaluated No. " + temp_es +  " to False " + "FFFFFFFFFFFFFFFFFFFFFFFFFF");
            }
        }
        
        my_logger.debug("End evaluate with ... No. " + temp_pos + "... Structure " + "\n");
    }

    // Private Methods
    //@ pure
    private final void preProcess() {
        // Formula Transformation
        my_logger.debug("Before Formula Transformation ---------------------\n" + my_formula.getFormula().toString());
        transformFormula(my_formula.getFormula());
        my_logger.debug("After Formula Transformation ---------------------\n" + my_formula.getFormula().toString());
    }
    
    //@ assignable my_auxiliary_predicate;
    private void transformFormula(final TemporalFormula a_formula) {
        if (a_formula == null) {
            return;
        }

        transformFormula(a_formula.getLeftTemporalSub());
        transformFormula(a_formula.getRightTemporalSub());
	    
	    if (a_formula.my_is_temporal) {
	        my_logger.debug("Transform Formula ----------" + a_formula.toString());
	        
	        final List temp_free_var = (LinkedList) a_formula.getFreeVariable();
	        final String[] temp_var = new String[temp_free_var.size()];
	        temp_free_var.toArray(temp_var);
	        String temp_formula_name = "p" + my_auxiliary_index;
	        my_signature.addPredicate(new Predicate(temp_formula_name, temp_var.length));
            a_formula.setAuxiliaryFormula(0, new AtomicFormula(temp_var, temp_formula_name, my_signature));
	        
            if (a_formula.getMainOperator().my_name.equals("S")) {
                final String[] temp_var2 = new String[temp_var.length+1];
                System.arraycopy(temp_var, 0, temp_var2, 0, temp_var.length);
                temp_var2[temp_var.length] = "r0";
            
                temp_formula_name = "r" + my_auxiliary_index;
                my_signature.addPredicate(new Predicate(temp_formula_name, temp_var2.length));
                a_formula.setAuxiliaryFormula(1, new AtomicFormula(temp_var2, 
                        temp_formula_name, my_signature));
            }
            
            if (a_formula.getMainOperator().my_name.equals("U")) {
                final String[] temp_var2 = new String[temp_var.length+1];
                System.arraycopy(temp_var, 0, temp_var2, 0, temp_var.length);
                temp_var2[temp_var.length] = "r0";
            
                temp_formula_name = "r" + my_auxiliary_index;
                my_signature.addPredicate(new Predicate(temp_formula_name, temp_var2.length));
                a_formula.setAuxiliaryFormula(1, new AtomicFormula(temp_var2, 
                        temp_formula_name, my_signature));
                
                final String[] temp_var3 = new String[temp_var.length+2];
                System.arraycopy(temp_var, 0, temp_var3, 0, temp_var.length);
                temp_var3[temp_var.length] = "s0";
                temp_var3[temp_var.length+1] = "s1";
                
                temp_formula_name = "s" + my_auxiliary_index;
                my_signature.addPredicate(new Predicate(temp_formula_name, temp_var3.length));
                a_formula.setAuxiliaryFormula(2, new AtomicFormula(temp_var3, 
                        temp_formula_name, my_signature));
            }
            
            my_auxiliary_index ++;
	    }
	}
	
    private int extendStructure(final TemporalFormula a_formula, final int a_pos) {
        if (a_formula == null) {
            return my_ats2.getSize();
        }
        
        int temp, temp2 = a_pos;
        if (a_formula.getMainOperator().my_name.equals("P") && a_pos > 0) {
            extendStructure(a_formula.getRightTemporalSub(), a_pos-1);
            extendP(a_formula, a_pos);
        } else if (a_formula.getMainOperator().my_name.equals("N")) {
            temp = extendStructure(a_formula.getRightTemporalSub(), a_pos);
            temp2 = (temp == my_ats2.getSize()) ? a_pos - 1 : temp -1;
            extendN(a_formula, temp2);
        } else if (a_formula.getMainOperator().my_name.equals("S")) {
            extendStructure(a_formula.getLeftTemporalSub(), a_pos);
            extendStructure(a_formula.getRightTemporalSub(), a_pos);
            extendS(a_formula, a_pos);
        } else if (a_formula.getMainOperator().my_name.equals("U")) {
            extendStructure(a_formula.getLeftTemporalSub(), a_pos);
            extendStructure(a_formula.getRightTemporalSub(), a_pos);
            
            temp2 = extendU(a_formula);
        } else if (ReservedSymbol.isFirstOrder(a_formula.getMainOperator().my_name)) {
            extendStructure(a_formula.getLeftTemporalSub(), a_pos);
            extendStructure(a_formula.getRightTemporalSub(), a_pos);
        }
        
        return temp2;
    }
    
	private void extendP(final TemporalFormula a_formula, final int a_pos) {
	    final Structure my_auxiliary_structure = my_ats2.getStructure(a_pos);
	    final String temp_formula_name = a_formula.getAuxiliaryFormula(0).getName(); 
	    final int temp_time_interval = my_ats2.getTime(a_pos) - my_ats2.getTime(a_pos-1);
        
        if (((TemporalOperator) a_formula.getMainOperator()).inRange(temp_time_interval)) {
            final Evaluation temp_ra = a_formula.getRightSubformula().evaluate(my_ats2.getStructure(a_pos-1));
            if (temp_ra.isTrue()) {
                my_auxiliary_structure.addNullaryRelation(temp_formula_name);
            } else if (!temp_ra.getSet().isEmpty()){
                my_auxiliary_structure.initRelationAssign(temp_formula_name);
                my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_ra.getSet());
            }
        } else {
            my_logger.warning("Security Policy NOT followed! ------- Time Interval: " + temp_time_interval);
        }
    }

    private void extendN(final TemporalFormula a_formula, final int a_pos) {
        if (a_pos < 0 || my_ats2.getSize() < 2) {
            return;
        }
        
        my_logger.warning("Security Policy Not followed! -------^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ Time Interval: " + a_pos);
        final Structure my_auxiliary_structure = my_ats2.getStructure(a_pos);
        final String temp_formula_name = a_formula.getAuxiliaryFormula(0).getName();
        final int temp_time_interval = my_ats2.getTime(a_pos + 1) - my_ats2.getTime(a_pos);
        
        if (((TemporalOperator)a_formula.getMainOperator()).inRange(temp_time_interval)) {
            final Evaluation temp_ra = a_formula.getRightSubformula().evaluate(my_ats2.getStructure(a_pos+1));
            if (temp_ra.isTrue()) {
                my_auxiliary_structure.addNullaryRelation(temp_formula_name);
                my_logger.warning("Security Policy Not followed! -------!!!!!!!!!!!!!!!!!!!!!!!!!!!!1" + my_auxiliary_structure.toString());
            } else if (!temp_ra.getSet().isEmpty()) {
                my_auxiliary_structure.initRelationAssign(temp_formula_name);
                my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_ra.getSet());
            }
        } else {
            my_logger.warning("Security Policy Not followed! ------- Time Interval: " + temp_time_interval);
        }
    }
   
    private int extendS(final TemporalFormula a_formula, final int a_pos) {
        final String temp_formula_name = a_formula.getAuxiliaryFormula(1).getName();
        
        final Structure my_auxiliary_structure = my_ats2.getStructure(a_pos);
        my_auxiliary_structure.initRelationAssign(temp_formula_name);
        
        // gama ^ Di * {0}, get r()
        final Evaluation gama0 = a_formula.getRightSubformula().evaluate(my_auxiliary_structure);
        if (gama0.isTrue()) {
            int[] temp_gama = {0};
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
            final int temp_time_interval = my_ats2.getTime(a_pos) - my_ats2.getTime(a_pos-1);

            // beta part
            final Evaluation beta_eval = a_formula.getLeftSubformula().evaluate(my_auxiliary_structure);
            final Set<int[]> beta = beta_eval.getSet();
            final Set<int[]> beta2 = my_ats2.getStructure(a_pos-1).getRelationAssign(temp_formula_name);
            
            if (beta2 == null) {
                return 0;
            } else {
                for (int[] i : beta2) {
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
            if (i[i.length-1] >= ((TemporalOperator)a_formula.getMainOperator()).getStart()) {
                final String temp_formula_name0 = a_formula.getAuxiliaryFormula(0).getName();
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
        
        return 0;
    }
    
    private int extendU(final TemporalFormula a_formula) {
        my_logger.warning("In Method extendU.....................");

        final Structure[] temp_structure = new Structure[my_ats2.getSize()];
        final String temp_formula_name = a_formula.getAuxiliaryFormula(2).getName(); //s
        
        for (int i = 0; i < my_ats2.getSize(); i++) {
            temp_structure[i] = new Structure();

            final Structure my_auxiliary_structure = my_ats2.getStructure(i);
            final Evaluation temp_ev = a_formula.getLeftSubformula().evaluate(my_auxiliary_structure);
            final Set<int[]> temp_r = temp_ev.getSet();
            if (temp_ev.isTrue()) {
                temp_structure[i].addNullaryRelation(temp_formula_name);
            } else if (!temp_r.isEmpty()) {
                    temp_structure[i].initRelationAssign(temp_formula_name);                    
                    temp_structure[i].addRelationAssign(temp_formula_name, temp_r);
            }
            my_logger.warning(" " + i + "::" + temp_structure[i].toString());
        }
        
        // compute l_i, the lookahead offset
        final int interval_start = ((TemporalOperator)a_formula.getMainOperator()).getStart();
        final int interval_end = ((TemporalOperator)a_formula.getMainOperator()).getEnd();
        final int[] lookahead_offset = getLookahead(interval_end);
        
        // decide the newest update
        final int a_pos = getPosExtendU(lookahead_offset);
        
        if (newInExtendU(lookahead_offset)) {
            my_logger.warning("Not new structure for evaluation");
            return -1;
        }

        if (a_pos == 0) {
            extendU0();
        }
        
        if (a_pos == 1) {
            extendU1(a_formula, lookahead_offset, a_pos, interval_start, temp_structure);
        }
        
        if (a_pos > 1) {
            extendU2(a_formula, lookahead_offset, a_pos, interval_start, temp_structure);
        }
        
        getPExtendU(a_formula, a_pos);

        my_logger.warning("Out Method extendU.....................");
        return a_pos;
    }
    
    private int extendU0() {
        return 0;
    }
    
    private int extendU1(final TemporalFormula a_formula, final int[] lookahead_offset, 
            final int a_pos, final int interval_start, final Structure[] temp_structure) {
        final Structure my_auxiliary_structure = my_ats2.getStructure(a_pos);
        String temp_formula_name = a_formula.getAuxiliaryFormula(1).getName(); //r
        my_auxiliary_structure.initRelationAssign(temp_formula_name);

        // new_r
        for (int i = 0; i <= lookahead_offset[a_pos]; i++) { // l_i-1 <= j <= l_i, where i=0, l_-1 = 0
            if ((my_ats2.getTime(a_pos+i) - my_ats2.getTime(a_pos)) >= interval_start) { // t_i+j - t_i >= c
                final Evaluation temp_ev = a_formula.getRightSubformula().evaluate(my_ats2.getStructure(i+a_pos));
                if (temp_ev.isTrue()) {
                    final int[] temp_array = {i};
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
        int pos_j, pos_j2;
        final Set<int[]> new_s = new HashSet();
        temp_formula_name = a_formula.getAuxiliaryFormula(2).getName();
        my_auxiliary_structure.initRelationAssign(temp_formula_name);
        
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

        // update_s = EMPTY
            
        return 1;
    }
    
    private int extendU2(final TemporalFormula a_formula, final int[] lookahead_offset, 
            final int a_pos, final int interval_start, final Structure[] temp_structure) {
        final Structure my_auxiliary_structure = my_ats2.getStructure(a_pos);
        String temp_formula_name = a_formula.getAuxiliaryFormula(1).getName(); //r
        my_auxiliary_structure.initRelationAssign(temp_formula_name);

        // new_r
        for (int i = lookahead_offset[a_pos-1]; i <= lookahead_offset[a_pos]; i++) { // l_i-1 <= j <= l_i, where i = pos
            if ((my_ats2.getTime(i + a_pos) - my_ats2.getTime(a_pos)) >= interval_start) {
                final Evaluation temp_ev = a_formula.getRightSubformula().evaluate(my_ats2.getStructure(i+a_pos));
                if (temp_ev.isTrue()) {
                    final int[] temp_array = {i};
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
        final Set<int[]> temp_r = my_ats2.getStructure(a_pos-1).getRelationAssign(temp_formula_name);
        for (int[] i : temp_r) {
            int[] copy_i = new int[i.length];
            System.arraycopy(i, 0, copy_i, 0, i.length);
            copy_i[i.length-1] = i[i.length-1] - 1;
            if (copy_i[i.length-1] < 0) {
                continue;
            }
            if ((my_ats2.getTime(copy_i[i.length-1]+a_pos) - my_ats2.getTime(a_pos)) >= interval_start) {
                my_auxiliary_structure.addRelationAssign(temp_formula_name, copy_i);
            }
        }
        
        
        // get s() := new_s + update_s        
        int pos_j, pos_j2;
        final Set<int[]> new_s = new HashSet();
        final Set<int[]> update_s = new HashSet();
        temp_formula_name = a_formula.getAuxiliaryFormula(2).getName();
        my_auxiliary_structure.initRelationAssign(temp_formula_name);

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
        
        // update_s
        final Set<int[]> set_temp = my_ats2.getStructure(a_pos-1).getRelationAssign(temp_formula_name);
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
            
        return 2;
    }
    
    private int[] getLookahead(final int the_interval_end) {
        int[] lookahead_offset = new int[my_ats2.getSize()];
        for (int i = 0; i < my_ats2.getSize(); i++) {
            for (int j = i; j < my_ats2.getSize(); j++) {
                if (my_ats2.getTime(j) - my_ats2.getTime(i) < the_interval_end) {
                    lookahead_offset[i] = j - i;
                } else {
                    break;
                }
            }
            my_logger.warning("Lookahead " + i + " : " + lookahead_offset[i]);
        }
        return lookahead_offset;
    }
    
    private int getPosExtendU(final int[] the_lookahead) {
        int a_pos = 0;
        for (int i = 1; i < the_lookahead.length; i++) {
            if (i + the_lookahead[i] < the_lookahead.length) {
                a_pos = i;
            } else {
                break;
            }
        }
        return a_pos;
    }
    
    private boolean newInExtendU(final int[] the_lookahead) {
        final int a_pos0 = getPosExtendU(the_lookahead);
        // TODO update
        return a_pos0 == 0;
    }
    
    private void getPExtendU(final TemporalFormula a_formula, final int a_pos) {
        // get s() := new_s + update_s        
        final Structure my_auxiliary_structure = my_ats2.getStructure(a_pos);
        int pos_j, pos_j2;
        String temp_formula_name = a_formula.getAuxiliaryFormula(2).getName();
        my_auxiliary_structure.initRelationAssign(temp_formula_name);

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