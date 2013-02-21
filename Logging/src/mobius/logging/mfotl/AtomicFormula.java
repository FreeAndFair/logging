package mobius.logging.mfotl;

/*
 * Class Atomic_Formula
 * 
 * for the leave notes of formula
 */

public class AtomicFormula extends Formula{
    public final Predicator predicator;
    public boolean value = false;
    private static final Logger my_logger = new Logger();
    
    public AtomicFormula(final String[] _var, final int _arity, final String _operator) {
        super();
        
        my_logger.info("\nBuild atomic formula");
        my_logger.debug(_var);
        my_logger.debug(_operator);
        
        predicator = new Predicator(_operator, _arity, _var);
    }
    
    public AtomicFormula(final String[] _formula) {
        super();
        
        my_logger.info("\nBuild atomic formula");        
        my_logger.debug(_formula);
        
        if (_formula[1].equals("=") || _formula[1].equals("<")) {
            final String[] _var_tmp = {_formula[0], _formula[2]};
            predicator = new Predicator(_formula[1], 2, _var_tmp);
        } else {
            String[] _var_tmp = new String[(_formula.length-2)/2];
            for (int i = 0; i < _var_tmp.length; i++) {
                _var_tmp[i] = _formula[(i+1)*2];
            }
            predicator = new Predicator(_formula[0], _var_tmp.length , _var_tmp);
        }
    }
    
    public boolean evaluateFormula(final Structure _structure) {
        value = predicator.evaluate(_structure);
        return value;
    }
    
    public String toString() {
        return (predicator.toString());
    }
}
