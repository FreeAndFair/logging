package demtech.mfotl;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

public class Monitor {
    // Attributes
    private static int my_auxiliary_index = 0;
    final private Signature my_signature;
    final private MFOTLFormula my_formula;
    final private TemporalStructure my_ats2 = new TemporalStructure();
    
    final private Logger my_logger = new Logger(); 
    
    // Constructors
    //@ assignable my_signature;
    //@ assignable my_formula;
    public Monitor(final String a_formula, final Signature a_signature) {
        my_signature = a_signature;
        my_formula = new MFOTLFormula(a_formula, my_signature);
        
        my_logger.debug("Before Formula Transformation ---------------------\n" + my_formula.getFormula().toString());
        transformFormula(my_formula.getFormula());
        my_logger.debug("After Formula Transformation ---------------------\n" + my_formula.getFormula().toString());
    }
    
    // Public Methods
    public boolean addStructure(final Structure a_structure, final int a_time_stamp) {
        boolean result = true;
        my_ats2.insertStructure(a_structure, a_time_stamp);
        final int temp_pos = my_ats2.getSize() - 1;
        final int temp_es = extendStructure(my_formula.getFormula(), temp_pos);
        my_logger.debug("Start evaluate with ... No. " + temp_pos + " with Structure : " + temp_es);
        
        if (temp_es < 0) {
            my_logger.warning("Unable to evaluate Formula with ... No. " + temp_pos + " ... Structure");
        } else {
            final Structure my_auxiliary_structure = my_ats2.getStructure(temp_es);
            my_logger.debug("Extended Structure: " + my_auxiliary_structure.toString() + " @Time: " + my_ats2.getTime(temp_es));
            
            my_logger.warning("Evaluating with Structure No. " + temp_es);
            if (my_formula.evaluateTruth(my_auxiliary_structure)){
                my_logger.warning("Evaluated No. " + temp_es +  " to True " + "TTTTTTTTTTTTTTTTTTTTTTTTTT");
            } else {
                result = false;
                my_logger.warning("Evaluated No. " + temp_es +  " to False " + "FFFFFFFFFFFFFFFFFFFFFFFFFF");
            }
        }

        my_logger.debug("End evaluate with ... No. " + temp_pos + "... Structure " + "\n");
        return result;
    }

    // Private Methods
   
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
	        my_signature.addPredicate(new Predicate(temp_formula_name, temp_var.length), null);
            a_formula.setAuxiliaryFormula(0, new AtomicFormula(temp_var, temp_formula_name, my_signature));
	        
            if (a_formula.getMainOperator().my_name.equals("S")) {
                final String[] temp_var2 = new String[temp_var.length+1];
                System.arraycopy(temp_var, 0, temp_var2, 0, temp_var.length);
                temp_var2[temp_var.length] = "r0";
            
                temp_formula_name = "r" + my_auxiliary_index;
                my_signature.addPredicate(new Predicate(temp_formula_name, temp_var2.length), null);
                a_formula.setAuxiliaryFormula(1, new AtomicFormula(temp_var2, 
                        temp_formula_name, my_signature));
            }
            
            if (a_formula.getMainOperator().my_name.equals("U")) {
                final String[] temp_var2 = new String[temp_var.length+1];
                System.arraycopy(temp_var, 0, temp_var2, 0, temp_var.length);
                temp_var2[temp_var.length] = "r0";
            
                temp_formula_name = "r" + my_auxiliary_index;
                my_signature.addPredicate(new Predicate(temp_formula_name, temp_var2.length), null);
                a_formula.setAuxiliaryFormula(1, new AtomicFormula(temp_var2, 
                        temp_formula_name, my_signature));
                
                final String[] temp_var3 = new String[temp_var.length+2];
                System.arraycopy(temp_var, 0, temp_var3, 0, temp_var.length);
                temp_var3[temp_var.length] = "s0";
                temp_var3[temp_var.length+1] = "s1";
                
                temp_formula_name = "s" + my_auxiliary_index;
                my_signature.addPredicate(new Predicate(temp_formula_name, temp_var3.length), null);
                a_formula.setAuxiliaryFormula(2, new AtomicFormula(temp_var3, 
                        temp_formula_name, my_signature));
            }
            
            my_auxiliary_index ++;
	    }
	}
	
    private int extendStructure(final TemporalFormula a_formula, final int a_pos) {
        if (a_formula == null || a_formula.getMainOperator() == null) {
            return my_ats2.getSize()-1;
        }
        
        if (ReservedSymbol.isTemporal(a_formula.getMainOperator().my_name)) {
            return extendStructureforTemporal(a_formula, a_pos);
        } else {
            my_logger.debug("Extend Other");
            int temp1 = extendStructure(a_formula.getLeftTemporalSub(), a_pos);
            final int temp2 = extendStructure(a_formula.getRightTemporalSub(), a_pos);
            temp1 = (temp2 < temp1) ? temp2 : temp1;
            return temp1;
        }
    }
    
    private int extendStructureforTemporal(final TemporalFormula a_formula, final int a_pos) {
        if (a_formula.getMainOperator().my_name.equals("P") && a_pos > 0) {
            my_logger.debug("Extend P");
            extendStructure(a_formula.getRightTemporalSub(), a_pos-1);
            extendP(a_formula, a_pos);
        } else if (a_formula.getMainOperator().my_name.equals("N")) {
            my_logger.debug("Extend N");
            final int temp = extendStructure(a_formula.getRightTemporalSub(), a_pos);
            final int temp2 = (temp == my_ats2.getSize()) ? a_pos - 1 : temp -1;
            extendN(a_formula, temp2);
            return temp2;
        } else if (a_formula.getMainOperator().my_name.equals("S")) {
            my_logger.debug("Extend S");
            extendStructure(a_formula.getLeftTemporalSub(), a_pos);
            extendStructure(a_formula.getRightTemporalSub(), a_pos);
            extendS(a_formula, a_pos);
        } else if (a_formula.getMainOperator().my_name.equals("U")) {
            my_logger.debug("Extend U");
            extendStructure(a_formula.getLeftTemporalSub(), a_pos);
            extendStructure(a_formula.getRightTemporalSub(), a_pos);
            return extendU(a_formula, a_pos);
        } 
        
        return a_pos;
    }
    
	private void extendP(final TemporalFormula a_formula, final int a_pos) {
	    my_logger.warning("InMethod extendP: a_pos = " + a_pos);
	    
	    final int temp_time_interval = my_ats2.getTime(a_pos) - my_ats2.getTime(a_pos-1);
        
        if (((TemporalOperator) a_formula.getMainOperator()).inRange(temp_time_interval)) {
            final Evaluation temp_ra = a_formula.getRightSubformula().evaluate(my_ats2.getStructure(a_pos-1));
            final Set<int[]> set0 = temp_ra.getSet();
            
            if (temp_ra.isTrue() && set0.isEmpty()) {
                final Structure my_auxiliary_structure = my_ats2.getStructure(a_pos);
                final String temp_formula_name = a_formula.getAuxiliaryFormula(0).getName(); 
                my_auxiliary_structure.addNullaryRelation(temp_formula_name);
            } else if (!set0.isEmpty()){
                final Structure my_auxiliary_structure = my_ats2.getStructure(a_pos);
                final String temp_formula_name = a_formula.getAuxiliaryFormula(0).getName(); 
                my_auxiliary_structure.initRelationAssign(temp_formula_name);
                my_auxiliary_structure.addRelationAssign(temp_formula_name, set0);
            }
        } else {
            my_logger.warning("Security Policy NOT followed! ------- Time Interval: " + temp_time_interval);
        }
    }

    private void extendN(final TemporalFormula a_formula, final int a_pos) {
        if (a_pos < 0 || my_ats2.getSize() < 2) {
            return;
        }
        
        my_logger.warning("InMethod extendN: a_pos = " + a_pos);

        final int temp_time_interval = my_ats2.getTime(a_pos + 1) - my_ats2.getTime(a_pos);
        
        if (((TemporalOperator)a_formula.getMainOperator()).inRange(temp_time_interval)) {
            final Evaluation temp_ra = a_formula.getRightSubformula().evaluate(my_ats2.getStructure(a_pos+1));
            final Set<int[]> set0 = temp_ra.getSet();
            
            if (temp_ra.isTrue() && set0.isEmpty()) {
                final Structure my_auxiliary_structure = my_ats2.getStructure(a_pos);
                final String temp_formula_name = a_formula.getAuxiliaryFormula(0).getName();
                my_auxiliary_structure.addNullaryRelation(temp_formula_name);
            } else if (!set0.isEmpty()) {
                final Structure my_auxiliary_structure = my_ats2.getStructure(a_pos);
                final String temp_formula_name = a_formula.getAuxiliaryFormula(0).getName();
                my_auxiliary_structure.initRelationAssign(temp_formula_name);
                my_auxiliary_structure.addRelationAssign(temp_formula_name, set0);
            }
        } else {
            my_logger.warning("Security Policy Not followed! ------- Time Interval: " + temp_time_interval);
        }
    }
   
    private void extendS(final TemporalFormula a_formula, final int a_pos) {
        final String temp_formula_name = a_formula.getAuxiliaryFormula(1).getName();
        
        final Structure my_auxiliary_structure = my_ats2.getStructure(a_pos);
        my_auxiliary_structure.initRelationAssign(temp_formula_name);
        
        // gama ^ Di * {0}, get r()
        final Evaluation gama0 = a_formula.getRightSubformula().evaluate(my_auxiliary_structure);
        final Set<int[]> set0 = gama0.getSet();
        
        if (gama0.isTrue() && set0.isEmpty()) {
            final int[] temp_gama = {0};
            my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_gama);
        } else {
            for (int[] i : set0) {
                int[] temp_gama = new int[i.length+1];
                System.arraycopy(i, 0, temp_gama, 0, i.length);
                temp_gama[i.length] = 0;
                my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_gama);
            }
        }
        
        if (a_pos > 0) {
            extendS2(a_formula, a_pos);
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
                    my_auxiliary_structure.addRelationAssign(temp_formula_name0, temp_j);
                }
            }
        }
    }

    private void extendS2(final TemporalFormula a_formula, final int a_pos) {
        final Structure my_auxiliary_structure = my_ats2.getStructure(a_pos);
        final String temp_formula_name = a_formula.getAuxiliaryFormula(1).getName();

        // beta part
        final Evaluation beta_eval = a_formula.getLeftSubformula().evaluate(my_auxiliary_structure);
        final Set<int[]> beta = beta_eval.getSet();
        final Set<int[]> beta2 = my_ats2.getStructure(a_pos-1).getRelationAssign(temp_formula_name);
        
        if (beta2 == null) {
            return;
        } else {
            for (int[] i : beta2) {
                final int[] temp_gama2 = new int[i.length-1];
                System.arraycopy(i, 0, temp_gama2, 0, temp_gama2.length);
                if (beta_eval.isTrue() || beta.contains(temp_gama2)) {
                    int[] temp_gama = new int[i.length];
                    System.arraycopy(i, 0, temp_gama, 0, i.length);
                    temp_gama[i.length-1] += my_ats2.getTime(a_pos) - my_ats2.getTime(a_pos-1);
                    my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_gama);
                }
            }
        }
    }
    
    private int extendU(final TemporalFormula a_formula, final int a_pos) {
        my_logger.debug("In Method extendU.....................");

        newRExtendU(a_formula, a_pos);
        final int temp_pos = newSExtendU(a_formula, a_pos);
        for (int i = 0; i < my_ats2.getSize(); i ++) {
            getPExtendU(a_formula, i);
        }
        my_logger.warning("After Method extendU....................." + my_ats2.toString());

        my_logger.warning("Out Method extendU....................." + (temp_pos - 1));
        return temp_pos - 1;
    }
    
    private void newRExtendU(final TemporalFormula a_formula, final int a_pos) {
        final String temp_formula_name = a_formula.getAuxiliaryFormula(1).getName(); //r
        final Structure my_auxiliary_structure = my_ats2.getStructure(a_pos);
        final Evaluation temp_ev = a_formula.getRightSubformula().evaluate(my_ats2.getStructure(a_pos));

        if (temp_ev.isTrue()) {
            final int[] temp_array = {0};
            my_auxiliary_structure.initRelationAssign(temp_formula_name);
            my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_array);
            updateRExtendU(a_formula, a_pos, temp_array);
        } else {
            final Set<int[]> temp_r = temp_ev.getSet();
            for (int[] j : temp_r) {
                int[] temp_j = new int[j.length + 1];
                System.arraycopy(j, 0, temp_j, 0, j.length);
                temp_j[j.length] = 0;
                my_auxiliary_structure.initRelationAssign(temp_formula_name);
                my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_j);
                updateRExtendU(a_formula, a_pos, temp_j);
            }
        }
    }
    
    private void updateRExtendU(final TemporalFormula a_formula, final int a_pos, final int[] a_array) {
        final int interval_start = ((TemporalOperator)a_formula.getMainOperator()).getStart();
        final int interval_end = ((TemporalOperator)a_formula.getMainOperator()).getEnd();

        for (int i = a_pos - 1; i >= 0; i--) {
            if (my_ats2.getTime(a_pos) - my_ats2.getTime(i) < interval_start) {
                return;
            } else if (my_ats2.getTime(a_pos) - my_ats2.getTime(i) >= interval_end) {
                continue;
            } else {
                final Structure my_auxiliary_structure = my_ats2.getStructure(i);
                final String temp_formula_name = a_formula.getAuxiliaryFormula(1).getName(); //r
                my_auxiliary_structure.initRelationAssign(temp_formula_name);
                
                int[] temp_j = new int[a_array.length];
                System.arraycopy(a_array, 0, temp_j, 0, temp_j.length);
                temp_j[temp_j.length - 1] = a_pos - i;

                my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_j);
            }
        }
    }

    private int newSExtendU(final TemporalFormula a_formula, final int a_pos) {
        int temp_pos = a_pos;
        final String temp_formula_name = a_formula.getAuxiliaryFormula(2).getName();
        final Structure my_auxiliary_structure = my_ats2.getStructure(a_pos);
        final Evaluation temp_ev = a_formula.getLeftSubformula().evaluate(my_ats2.getStructure(a_pos));
        
        if (temp_ev.isTrue()) {
            final int[] temp_array = {0, 0};
            my_auxiliary_structure.initRelationAssign(temp_formula_name);
            my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_array);
            temp_pos = updateSExtendU(a_formula, a_pos, temp_array);
        } else {
            final Set<int[]> temp_r = temp_ev.getSet();
            for (int[] j : temp_r) {
                int[] temp_j = new int[j.length + 2];
                System.arraycopy(j, 0, temp_j, 0, j.length);
                temp_j[j.length] = 0;
                temp_j[j.length+1] = 0;
                my_auxiliary_structure.initRelationAssign(temp_formula_name);
                my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_j);
                final int temp_pos2 = updateSExtendU(a_formula, a_pos, temp_j);
                temp_pos = (temp_pos2 < temp_pos) ? temp_pos2:temp_pos;
            }
        }
        return temp_pos;
    }
    
    private int updateSExtendU(final TemporalFormula a_formula, final int a_pos, final int[] a_array) {
        int temp_pos = a_pos;
        for (int i = a_pos - 1; i >= 0; i--) {
            final String temp_formula_name = a_formula.getAuxiliaryFormula(2).getName();
            final Set<int[]> temp_set = my_ats2.getStructure(i).getRelationAssign(temp_formula_name);
            if (setContains(temp_set, a_array)) {
                final Structure my_auxiliary_structure = my_ats2.getStructure(i);
                int[] temp_j = new int[a_array.length];
                System.arraycopy(a_array, 0, temp_j, 0, a_array.length);
                temp_j[a_array.length-1] = a_pos - i;
                my_auxiliary_structure.initRelationAssign(temp_formula_name);
                my_auxiliary_structure.addRelationAssign(temp_formula_name, temp_j);
                temp_pos = i;
            } else {
                break;
            }
        }
        
        return temp_pos;
    }
    
    /* Not used
    private int[] getLookahead(final int the_interval_end) {
        final int[] lookahead_offset = new int[my_ats2.getSize()];
        for (int i = 0; i < my_ats2.getSize(); i++) {
            lookahead_offset[i] = -1;
            for (int j = i+1; j < my_ats2.getSize(); j++) {
                if (my_ats2.getTime(j) - my_ats2.getTime(i) < the_interval_end) {
                    lookahead_offset[i] = j - i;
                } else {
                    break;
                }
            }
            my_logger.warning("Lookahead " + i + " : " + lookahead_offset[i]);
        }
        
        return lookahead_offset;
    }*/
    
    private void getPExtendU(final TemporalFormula a_formula, final int a_pos) {
        // get s() := new_s + update_s
        final Structure my_auxiliary_structure = my_ats2.getStructure(a_pos);

        // get p()
        String temp_formula_name = a_formula.getAuxiliaryFormula(2).getName(); //s
        final Set<int[]> temp_sa = my_auxiliary_structure.getRelationAssign(temp_formula_name);
        temp_formula_name = a_formula.getAuxiliaryFormula(1).getName(); //r
        final Set<int[]> temp_ra = my_auxiliary_structure.getRelationAssign(temp_formula_name);
        
        if (temp_sa == null || temp_ra == null) {
            return;
        }

        for (int[] a_i : temp_ra) {
            final int[] a_temp = new int[a_i.length-1];
            System.arraycopy(a_i, 0, a_temp, 0, a_temp.length);
            for (int[] a_j : temp_sa) {
                final int pos_j = a_i[a_i.length-1];
                final int pos_j2 = a_j[a_j.length-1];
                if ((a_j[a_j.length-2] == 0) && (pos_j <= pos_j2+1)) {
                    final int[] a_temp2 = new int[a_j.length -2];
                    System.arraycopy(a_j, 0, a_temp2, 0, a_temp2.length);
                    if (Arrays.equals(a_temp, a_temp2)) {
                        temp_formula_name = a_formula.getAuxiliaryFormula(0).getName();
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
    
    //@ pure
    private boolean setContains(final Set<int[]> a_set, final int[] a_array) {
        if (a_set == null || a_array == null) {
            return false;
        }
        for (int[] temp_i : a_set) {
            if (Arrays.equals(temp_i, a_array)) {
                return true;
            }
        }
        return false;
    }
}