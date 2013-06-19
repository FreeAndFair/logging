package demtech.mfotl;

public class Formula {
    // Attributes
    protected boolean my_is_firstorder = true;
    protected boolean my_is_temporal = false;
    final private Logger my_logger = new Logger();
    
    // Public Methods
    protected Evaluation evaluate(final Structure a_structure) {
        my_logger.debug("InMethod: Formula.evaluate");
        return null;
    }
    
    public boolean isFirstorder() {
        return this.my_is_firstorder;
    }
    
    public boolean isTemporal() {
        return this.my_is_temporal;
    }
}
