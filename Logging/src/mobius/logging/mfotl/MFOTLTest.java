package mobius.logging.mfotl;

public class MFOTLTest {
    /**
     * @param args
     * 
     * Test for formula parsing and evaluating
     */
    public static void main(final String[] args) {
        //new Formula("A ( ! E x ( in (x) & ! ( E y ( y = y U [ 0 , 6 ) out ( x ) ) )  )  )");
        
        // test for free and bound variable
        new MFOTLFormula("E x z(in(x,y))");
        
        // test for temporal sub-formula
        new MFOTLFormula("(P (a=a))&((N (b=b))S[1,9)(c=c))");
        
        /*
        new Formula("! N[1,5)n(p) ");
        new Formula("N[1,5)n(p) ");
        new Formula("(x=y)&m(a,b)&N[3,5)n(p) ");
        
        new Formula("(( x = y ) &r ( m , n ) & ( z = x ) )");

        new Formula("   ( x < y )" );

        new Formula("( r ( a , b ) )");*/
        new MFOTLFormula("aar ( a , b , 5 )");
    }
}
