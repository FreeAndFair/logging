package mobius.logging.mfotl;

public class Monitor {
	void signatureExtension() {
		
	}
	
	void formulaTransformation() {
		
	}
	
	// the main monitor algorithm
	void runMonitor() {
	    int i = 0; // current index in input sequence (D0, t0)...
	    int q = 0; // index of next query evaluation in sequence (D0, t0) ...
	    //Q q_0 = new Q();
	    
	    
	    for (i=0; i < 10; i++) {
	        // carry over constants and relations of D_i to D'_i
	        
	    }
	}
	
	class Q {
	    Formula a; // alpha temporal sub-formula of phi
	    int j;     // index
	    Formula w; // waitfor(a)
	}
}
