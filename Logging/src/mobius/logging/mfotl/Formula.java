package mobius.logging.mfotl;

import java.util.Set;

public class Formula {
    // Attributes
    public boolean my_is_firstorder = true;
    public boolean my_is_temporal = false;
    protected Logger my_logger = new Logger();
    
    // Public Methods
    /**
     * return the truth value
     * @param a_structure
     * @return
     */
    public Set evaluate(final Structure a_structure) {
        my_logger.debug("InMethod: Formula.evaluate");
        return null;
    }
    
    
    /**
     * return the truth evaluation assignment
     * @param a_set
     * @param a_structure
     * @return
     */
    public Set evaluateExist(final Set a_set, final Structure a_structure) {
        my_logger.debug("InMethod: Formula.evaluateE");
        return null;
    }
}
