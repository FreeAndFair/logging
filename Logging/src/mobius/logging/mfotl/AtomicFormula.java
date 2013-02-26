package mobius.logging.mfotl;

/*
 * Class Atomic_Formula
 * 
 * for the leave notes of formula
 */

public class AtomicFormula extends Formula{
    public final Predicator my_predicator;
    public boolean my_value = false;
    private static final Logger my_logger = new Logger();
    
    public AtomicFormula(final String[] _var, final int _arity, final String _operator) {
        super();
        
        my_logger.info("\nBuild atomic formula");
        my_logger.debug(_var);
        my_logger.debug(_operator);
        
        my_predicator = new Predicator(_operator, _arity, _var);
    }
    
    public AtomicFormula(final String[] _formula) {
        super();
        
        my_logger.info("\nBuild atomic formula");        
        my_logger.debug(_formula);
        
        if (_formula[1].equals("=") || _formula[1].equals("<")) {
            final String[] _var_tmp = {_formula[0], _formula[2]};
            my_predicator = new Predicator(_formula[1], 2, _var_tmp);
        } else {
            String[] _var_tmp = new String[(_formula.length-2)/2];
            for (int i = 0; i < _var_tmp.length; i++) {
                _var_tmp[i] = _formula[(i+1)*2];
            }
            my_predicator = new Predicator(_formula[0], _var_tmp.length , _var_tmp);
        }
    }
    
    public boolean evaluateFormula(final Structure _structure) {
        my_value = my_predicator.evaluate(_structure);
        return my_value;
    }
    
    public String toString() {
        return (my_predicator.toString());
    }
}


/**
 * not used
 */

class Propsition {
    public String my_name;
    public boolean my_value;
    
    public Propsition(final String a_name) {
        my_name = a_name;
    }
}