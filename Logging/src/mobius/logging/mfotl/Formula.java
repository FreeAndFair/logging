package mobius.logging.mfotl;

import java.util.Set;

public class Formula {
    // Attributes
    public boolean my_is_firstorder = true;
    public boolean my_is_temporal = false;
    protected Logger my_logger = new Logger();
    
    // Public Methods
    public boolean evaluate(final Structure a_structure) {
        my_logger.debug("InMethod: Formula.evaluate");
        return false;
    }
    
    public boolean evaluateExist(final Set a_set, final Structure a_structure) {
        my_logger.debug("InMethod: Formula.exist");
        return false;
    }
}
