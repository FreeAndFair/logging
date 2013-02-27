package mobius.logging.mfotl;

import java.util.Set;

// TODO Implement the full algorithm

public class Monitor {
    // Attributes
    private MFOTLFormula my_formula;
    
    // Constructors    
    public Monitor(final String a_formula) {
        my_formula = new MFOTLFormula(a_formula);
        
        signatureExtension();
        
        formulaTransformation();
    }
    
    // Public Methods
    
    /**
     * the main monitor algorithm
     */
    public void runMonitor(StructureSequence a_structure_sequence) {
        int i = 0; // current index in input sequence (D0, t0)...
        int q = 0; // index of next query evaluation in sequence (D0, t0) ...
        //Q q_0 = new Q();
        
        
        for (i=0; i < 10; i++) {
            // carry over constants and relations of D_i to D'_i
            
        }
    }    

    // Private Methods
	private void signatureExtension() {
		/*
		 * R' = R Union {P_a|a temporal sub-formula of phi}
		 */
	    Set<Formula> temp_temporal_subformula = my_formula.my_temporal_subformula;
	    
	    for (Formula i : temp_temporal_subformula) {
	        /*
	         * Built new relation from temporal subformula (MFOTL, Basin et al. ,page 5)
	         * TODO update free variable
	         */
	        Predicator temp_predicate = new Predicator();
	        my_formula.my_signature.addPredicate(temp_predicate);
	    }
	}
	
	private void formulaTransformation() {
		
	}

	
	class Q {
	    MFOTLFormula a; // alpha temporal sub-formula of phi
	    int j;     // index
	    MFOTLFormula w; // waitfor(a)
	}
}
