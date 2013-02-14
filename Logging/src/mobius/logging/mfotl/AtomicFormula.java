package mobius.logging.mfotl;

/*
 * Class Atomic_Formula
 * 
 * for the leave notes of formula
 */

public class AtomicFormula {
    public final Predicate operator;
    
    public AtomicFormula(final String[] _var, final int _arity, final String _operator) {
        operator = new Predicate(_operator, _arity, _var);
    }
    
    public AtomicFormula(final String[] _formula) {
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
