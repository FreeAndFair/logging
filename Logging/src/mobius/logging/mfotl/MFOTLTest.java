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
        new Formula("E x(in(x,y))");
        /*
        new Formula("! N[1,5)n(p) ");
        new Formula("N[1,5)n(p) ");
        new Formula("(x=y)&m(a,b)&N[3,5)n(p) ");
        
        new Formula("(( x = y ) &r ( m , n ) & ( z = x ) )");

        new Formula("   ( x < y )" );

        new Formula("( r ( a , b ) )");
        new Formula("aar ( a , b , 5 )");*/
    }
}
