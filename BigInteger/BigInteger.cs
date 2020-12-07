using System;
using System.Security.Cryptography;
using System.IO;		//FileStream. (methods CompareFiles, EncryptFile, DecryptFile)
using System.Linq;		//Compare arrays SequenceEqual (method CompareBytes)
using System.Xml;		//to parse XML-keys, when this loading. (method LoadKeyFile)
using System.Xml.Linq;	//to parse XML-keys, when this loading. System.Xml.Linq.XElement (method LoadKeyFile)

// compile with: /doc:BigIntegerDocComment.xml

/// <summary>
/// This is a BigInteger class. Holds integer that is more than 64-bit (long).
/// </summary>
/// <remarks>
/// This class contains overloaded arithmetic operators(+, -, *, /, %), bitwise operators(&amp;, |) and other
/// operations that can be done with normal integer. It also contains implementation of various prime test.
/// This class also contains methods dealing with cryptography such as generating prime number, generating 
/// a coprime number.
/// </remarks>

public class BigInteger
{
    // maximum length of the BigInteger in uint (4 bytes)
    // change this to suit the required level of precision.

//    private const int maxLength = 70;
//	private const int maxLength = 16384;		// * 4	=	65536	=	524288 bits
	private const int maxLength = 2048;		// * 4	=	8192	=	16384 bits
//
//Test large BigInteger:
//		Random rnd2 = new Random();
//		Byte[] randbigint = new Byte[maxLength];	//with large values of "maxLength" BigInteger working slower...
//		rnd.NextBytes(randbigint);
//		log("test_large_BigInteger "+(new BigInteger(randbigint)).ToString());

    // primes smaller than 2000 to test the generated prime number
    public static readonly int[] primesBelow2000 = {
           2,    3,    5,    7,   11,   13,   17,   19,   23,   29,   31,   37,   41,   43,   47,   53,   59,   61,   67,   71,
          73,   79,   83,   89,   97,  101,  103,  107,  109,  113,  127,  131,  137,  139,  149,  151,  157,  163,  167,  173,
         179,  181,  191,  193,  197,  199,  211,  223,  227,  229,  233,  239,  241,  251,  257,  263,  269,  271,  277,  281,
         283,  293,  307,  311,  313,  317,  331,  337,  347,  349,  353,  359,  367,  373,  379,  383,  389,  397,  401,  409,
         419,  421,  431,  433,  439,  443,  449,  457,  461,  463,  467,  479,  487,  491,  499,  503,  509,  521,  523,  541,
         547,  557,  563,  569,  571,  577,  587,  593,  599,  601,  607,  613,  617,  619,  631,  641,  643,  647,  653,  659,
         661,  673,  677,  683,  691,  701,  709,  719,  727,  733,  739,  743,  751,  757,  761,  769,  773,  787,  797,  809,
         811,  821,  823,  827,  829,  839,  853,  857,  859,  863,  877,  881,  883,  887,  907,  911,  919,  929,  937,  941,
         947,  953,  967,  971,  977,  983,  991,  997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069,
        1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223,
        1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373,
        1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511,
        1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657,
        1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811,
        1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987,
        1993, 1997, 1999 };

    private uint[] data = null;            // stores bytes from the Big Integer
    public int dataLength;                 // number of actual chars used

    /// <summary>
    /// Default constructor for BigInteger of value 0
    /// </summary>
    public BigInteger()
    {
        data = new uint[maxLength];
        dataLength = 1;
    }


    /// <summary>
    /// Constructor (Default value provided by long)
    /// </summary>
    /// <param name="value">Turn the long value into BigInteger type</param>
    public BigInteger(long value)
    {
        data = new uint[maxLength];
        long tempVal = value;

        // copy bytes from long to BigInteger without any assumption of
        // the length of the long datatype
        dataLength = 0;
        while (value != 0 && dataLength < maxLength)
        {
            data[dataLength] = (uint)(value & 0xFFFFFFFF);
            value >>= 32;
            dataLength++;
        }

        if (tempVal > 0)         // overflow check for +ve value
        {
            if (value != 0 || (data[maxLength - 1] & 0x80000000) != 0)
                throw (new ArithmeticException("Positive overflow in constructor."));
        }
        else if (tempVal < 0)    // underflow check for -ve value
        {
            if (value != -1 || (data[dataLength - 1] & 0x80000000) == 0)
                throw (new ArithmeticException("Negative underflow in constructor."));
        }

        if (dataLength == 0)
            dataLength = 1;
    }


    /// <summary>
    /// Constructor (Default value provided by ulong)
    /// </summary>
    /// <param name="value">Turn the unsigned long value into BigInteger type</param>
    public BigInteger(ulong value)
    {
        data = new uint[maxLength];

        // copy bytes from ulong to BigInteger without any assumption of
        // the length of the ulong datatype
        dataLength = 0;
        while (value != 0 && dataLength < maxLength)
        {
            data[dataLength] = (uint)(value & 0xFFFFFFFF);
            value >>= 32;
            dataLength++;
        }

        if (value != 0 || (data[maxLength - 1] & 0x80000000) != 0)
            throw (new ArithmeticException("Positive overflow in constructor."));

        if (dataLength == 0)
            dataLength = 1;
    }


    /// <summary>
    /// Constructor (Default value provided by BigInteger)
    /// </summary>
    /// <param name="bi"></param>
    public BigInteger(BigInteger bi)
    {
        data = new uint[maxLength];

        dataLength = bi.dataLength;

        for (int i = 0; i < dataLength; i++)
            data[i] = bi.data[i];
    }


    /// <summary>
    /// Constructor (Default value provided by a string of digits of the specified base)
    /// </summary>
    /// <example>
    /// To initialize "a" with the default value of 1234 in base 10:
    ///      BigInteger a = new BigInteger("1234", 10)
    /// To initialize "a" with the default value of -0x1D4F in base 16:
    ///      BigInteger a = new BigInteger("-1D4F", 16)
    /// </example>
    /// 
    /// <param name="value">String value in the format of [sign][magnitude]</param>
    /// <param name="radix">The base of value</param>
    public BigInteger(string value, int radix)
    {
        BigInteger multiplier = new BigInteger(1);
        BigInteger result = new BigInteger();
        value = (value.ToUpper()).Trim();
        int limit = 0;

        if (value[0] == '-')
            limit = 1;

        for (int i = value.Length - 1; i >= limit; i--)
        {
            int posVal = (int)value[i];

            if (posVal >= '0' && posVal <= '9')
                posVal -= '0';
            else if (posVal >= 'A' && posVal <= 'Z')
                posVal = (posVal - 'A') + 10;
            else
                posVal = 9999999;       // arbitrary large


            if (posVal >= radix)
                throw (new ArithmeticException("Invalid string in constructor."));
            else
            {
                if (value[0] == '-')
                    posVal = -posVal;

                result = result + (multiplier * posVal);

                if ((i - 1) >= limit)
                    multiplier = multiplier * radix;
            }
        }

        if (value[0] == '-')     // negative values
        {
            if ((result.data[maxLength - 1] & 0x80000000) == 0)
                throw (new ArithmeticException("Negative underflow in constructor."));
        }
        else    // positive values
        {
            if ((result.data[maxLength - 1] & 0x80000000) != 0)
                throw (new ArithmeticException("Positive overflow in constructor."));
        }

        data = new uint[maxLength];
        for (int i = 0; i < result.dataLength; i++)
            data[i] = result.data[i];

        dataLength = result.dataLength;
    }


    //***********************************************************************
    // Constructor (Default value provided by an array of bytes)
    //
    // The lowest index of the input byte array (i.e [0]) should contain the
    // most significant byte of the number, and the highest index should
    // contain the least significant byte.
    //
    // E.g.
    // To initialize "a" with the default value of 0x1D4F in base 16
    //      byte[] temp = { 0x1D, 0x4F };
    //      BigInteger a = new BigInteger(temp)
    //
    // Note that this method of initialization does not allow the
    // sign to be specified.
    //
    //***********************************************************************
    /*public BigInteger(byte[] inData)
    {
        dataLength = inData.Length >> 2;

        int leftOver = inData.Length & 0x3;
        if (leftOver != 0)         // length not multiples of 4
            dataLength++;


        if (dataLength > maxLength)
            throw (new ArithmeticException("Byte overflow in constructor."));

        data = new uint[maxLength];

        for (int i = inData.Length - 1, j = 0; i >= 3; i -= 4, j++)
        {
            data[j] = ((uint)(inData[i - 3]) << 24) + ((uint)(inData[i - 2]) << 16) +
                      ((uint)(inData[i - 1] << 8))  + ((uint)(inData[i]));
        }

        if (leftOver == 1)
            data[dataLength - 1] = (uint)inData[0];
        else if (leftOver == 2)
            data[dataLength - 1] = (uint)((inData[0] << 8) + inData[1]);
        else if (leftOver == 3)
            data[dataLength - 1] = (uint)((inData[0] << 16) + (inData[1] << 8) + inData[2]);


        while (dataLength > 1 && data[dataLength - 1] == 0)
            dataLength--;
    }*/


    /// <summary>
    /// Constructor (Default value provided by an array of bytes of the specified length.)
    /// </summary>
    /// <param name="inData">A list of byte values</param>
    /// <param name="length">Default -1</param>
    /// <param name="offset">Default 0</param>
    public BigInteger(System.Collections.Generic.IList<byte> inData, int length = -1, int offset = 0)
    {
        var inLen = length == -1 ? inData.Count - offset : length;

        dataLength = inLen >> 2;

        int leftOver = inLen & 0x3;
        if (leftOver != 0)         // length not multiples of 4
            dataLength++;

        if (dataLength > maxLength || inLen > inData.Count - offset)
            throw (new ArithmeticException("Byte overflow in constructor."));


        data = new uint[maxLength];

        for (int i = inLen - 1, j = 0; i >= 3; i -= 4, j++)
        {
            data[j] = (uint)((inData[offset + i - 3] << 24) + (inData[offset + i - 2] << 16) +
                             (inData[offset + i - 1] << 8) + inData[offset + i]);
        }

        if (leftOver == 1)
            data[dataLength - 1] = (uint)inData[offset + 0];
        else if (leftOver == 2)
            data[dataLength - 1] = (uint)((inData[offset + 0] << 8) + inData[offset + 1]);
        else if (leftOver == 3)
            data[dataLength - 1] = (uint)((inData[offset + 0] << 16) + (inData[offset + 1] << 8) + inData[offset + 2]);


        if (dataLength == 0)
            dataLength = 1;

        while (dataLength > 1 && data[dataLength - 1] == 0)
            dataLength--;
    }


    /// <summary>
    ///  Constructor (Default value provided by an array of unsigned integers)
    /// </summary>
    /// <param name="inData">Array of unsigned integer</param>
    public BigInteger(uint[] inData)
    {
        dataLength = inData.Length;

        if (dataLength > maxLength)
            throw (new ArithmeticException("Byte overflow in constructor."));

        data = new uint[maxLength];

        for (int i = dataLength - 1, j = 0; i >= 0; i--, j++)
            data[j] = inData[i];

        while (dataLength > 1 && data[dataLength - 1] == 0)
            dataLength--;
    }


    /// <summary>
    /// Cast a type long value to type BigInteger value
    /// </summary>
    /// <param name="value">A long value</param>
    public static implicit operator BigInteger(long value)
    {
        return (new BigInteger(value));
    }


    /// <summary>
    /// Cast a type ulong value to type BigInteger value
    /// </summary>
    /// <param name="value">An unsigned long value</param>
    public static implicit operator BigInteger(ulong value)
    {
        return (new BigInteger(value));
    }


    /// <summary>
    /// Cast a type int value to type BigInteger value
    /// </summary>
    /// <param name="value">An int value</param>
    public static implicit operator BigInteger(int value)
    {
        return (new BigInteger((long)value));
    }


    /// <summary>
    /// Cast a type uint value to type BigInteger value
    /// </summary>
    /// <param name="value">An unsigned int value</param>
    public static implicit operator BigInteger(uint value)
    {
        return (new BigInteger((ulong)value));
    }


    /// <summary>
    /// Overloading of addition operator
    /// </summary>
    /// <param name="bi1">First BigInteger</param>
    /// <param name="bi2">Second BigInteger</param>
    /// <returns>Result of the addition of 2 BigIntegers</returns>
    public static BigInteger operator +(BigInteger bi1, BigInteger bi2)
    {
        BigInteger result = new BigInteger()
        {
            dataLength = (bi1.dataLength > bi2.dataLength) ? bi1.dataLength : bi2.dataLength
        };

        long carry = 0;
        for (int i = 0; i < result.dataLength; i++)
        {
            long sum = (long)bi1.data[i] + (long)bi2.data[i] + carry;
            carry = sum >> 32;
            result.data[i] = (uint)(sum & 0xFFFFFFFF);
        }

        if (carry != 0 && result.dataLength < maxLength)
        {
            result.data[result.dataLength] = (uint)(carry);
            result.dataLength++;
        }

        while (result.dataLength > 1 && result.data[result.dataLength - 1] == 0)
            result.dataLength--;


        // overflow check
        int lastPos = maxLength - 1;
        if ((bi1.data[lastPos] & 0x80000000) == (bi2.data[lastPos] & 0x80000000) &&
           (result.data[lastPos] & 0x80000000) != (bi1.data[lastPos] & 0x80000000))
        {
            throw (new ArithmeticException());
        }

        return result;
    }


    /// <summary>
    /// Overloading of the unary ++ operator, which increments BigInteger by 1
    /// </summary>
    /// <param name="bi1">A BigInteger</param>
    /// <returns>Incremented BigInteger</returns>
    public static BigInteger operator ++(BigInteger bi1)
    {
        BigInteger result = new BigInteger(bi1);

        long val, carry = 1;
        int index = 0;

        while (carry != 0 && index < maxLength)
        {
            val = (long)(result.data[index]);
            val++;

            result.data[index] = (uint)(val & 0xFFFFFFFF);
            carry = val >> 32;

            index++;
        }

        if (index > result.dataLength)
            result.dataLength = index;
        else
        {
            while (result.dataLength > 1 && result.data[result.dataLength - 1] == 0)
                result.dataLength--;
        }

        // overflow check
        int lastPos = maxLength - 1;

        // overflow if initial value was +ve but ++ caused a sign
        // change to negative.

        if ((bi1.data[lastPos] & 0x80000000) == 0 &&
           (result.data[lastPos] & 0x80000000) != (bi1.data[lastPos] & 0x80000000))
        {
            throw (new ArithmeticException("Overflow in ++."));
        }
        return result;
    }


    /// <summary>
    /// Overloading of subtraction operator
    /// </summary>
    /// <param name="bi1">First BigInteger</param>
    /// <param name="bi2">Second BigInteger</param>
    /// <returns>Result of the subtraction of 2 BigIntegers</returns>
    public static BigInteger operator -(BigInteger bi1, BigInteger bi2)
    {
        BigInteger result = new BigInteger()
        {
            dataLength = (bi1.dataLength > bi2.dataLength) ? bi1.dataLength : bi2.dataLength
        };

        long carryIn = 0;
        for (int i = 0; i < result.dataLength; i++)
        {
            long diff;

            diff = (long)bi1.data[i] - (long)bi2.data[i] - carryIn;
            result.data[i] = (uint)(diff & 0xFFFFFFFF);

            if (diff < 0)
                carryIn = 1;
            else
                carryIn = 0;
        }

        // roll over to negative
        if (carryIn != 0)
        {
            for (int i = result.dataLength; i < maxLength; i++)
                result.data[i] = 0xFFFFFFFF;
            result.dataLength = maxLength;
        }

        // fixed in v1.03 to give correct datalength for a - (-b)
        while (result.dataLength > 1 && result.data[result.dataLength - 1] == 0)
            result.dataLength--;

        // overflow check

        int lastPos = maxLength - 1;
        if ((bi1.data[lastPos] & 0x80000000) != (bi2.data[lastPos] & 0x80000000) &&
           (result.data[lastPos] & 0x80000000) != (bi1.data[lastPos] & 0x80000000))
        {
            throw (new ArithmeticException());
        }

        return result;
    }


    /// <summary>
    /// Overloading of the unary -- operator, decrements BigInteger by 1
    /// </summary>
    /// <param name="bi1">A BigInteger</param>
    /// <returns>Decremented BigInteger</returns>
    public static BigInteger operator --(BigInteger bi1)
    {
        BigInteger result = new BigInteger(bi1);

        long val;
        bool carryIn = true;
        int index = 0;

        while (carryIn && index < maxLength)
        {
            val = (long)(result.data[index]);
            val--;

            result.data[index] = (uint)(val & 0xFFFFFFFF);

            if (val >= 0)
                carryIn = false;

            index++;
        }

        if (index > result.dataLength)
            result.dataLength = index;

        while (result.dataLength > 1 && result.data[result.dataLength - 1] == 0)
            result.dataLength--;

        // overflow check
        int lastPos = maxLength - 1;

        // overflow if initial value was -ve but -- caused a sign
        // change to positive.

        if ((bi1.data[lastPos] & 0x80000000) != 0 &&
           (result.data[lastPos] & 0x80000000) != (bi1.data[lastPos] & 0x80000000))
        {
            throw (new ArithmeticException("Underflow in --."));
        }

        return result;
    }


    /// <summary>
    /// Overloading of multiplication operator
    /// </summary>
    /// <param name="bi1">First BigInteger</param>
    /// <param name="bi2">Second BigInteger</param>
    /// <returns>Result of the multiplication of 2 BigIntegers</returns>
    public static BigInteger operator *(BigInteger bi1, BigInteger bi2)
    {
        int lastPos = maxLength - 1;
        bool bi1Neg = false, bi2Neg = false;

        // take the absolute value of the inputs
        try
        {
            if ((bi1.data[lastPos] & 0x80000000) != 0)     // bi1 negative
            {
                bi1Neg = true; bi1 = -bi1;
            }
            if ((bi2.data[lastPos] & 0x80000000) != 0)     // bi2 negative
            {
                bi2Neg = true; bi2 = -bi2;
            }
        }
        catch (Exception) { }

        BigInteger result = new BigInteger();

        // multiply the absolute values
        try
        {
            for (int i = 0; i < bi1.dataLength; i++)
            {
                if (bi1.data[i] == 0) continue;

                ulong mcarry = 0;
                for (int j = 0, k = i; j < bi2.dataLength; j++, k++)
                {
                    // k = i + j
                    ulong val = ((ulong)bi1.data[i] * (ulong)bi2.data[j]) +
                                 (ulong)result.data[k] + mcarry;

                    result.data[k] = (uint)(val & 0xFFFFFFFF);
                    mcarry = (val >> 32);
                }

                if (mcarry != 0)
                    result.data[i + bi2.dataLength] = (uint)mcarry;
            }
        }
        catch (Exception)
        {
            throw (new ArithmeticException("Multiplication overflow."));
        }


        result.dataLength = bi1.dataLength + bi2.dataLength;
        if (result.dataLength > maxLength)
            result.dataLength = maxLength;

        while (result.dataLength > 1 && result.data[result.dataLength - 1] == 0)
            result.dataLength--;

        // overflow check (result is -ve)
        if ((result.data[lastPos] & 0x80000000) != 0)
        {
            if (bi1Neg != bi2Neg && result.data[lastPos] == 0x80000000)    // different sign
            {
                // handle the special case where multiplication produces
                // a max negative number in 2's complement.

                if (result.dataLength == 1)
                    return result;
                else
                {
                    bool isMaxNeg = true;
                    for (int i = 0; i < result.dataLength - 1 && isMaxNeg; i++)
                    {
                        if (result.data[i] != 0)
                            isMaxNeg = false;
                    }

                    if (isMaxNeg)
                        return result;
                }
            }

            throw (new ArithmeticException("Multiplication overflow."));
        }

        // if input has different signs, then result is -ve
        if (bi1Neg != bi2Neg)
            return -result;

        return result;
    }


    /// <summary>
    /// Overloading of the unary &lt;&lt; operator (left shift)
    /// </summary>
    /// <remarks>
    /// Shifting by a negative number is an undefined behaviour (UB).
    /// </remarks>
    /// <param name="bi1">A BigInteger</param>
    /// <param name="shiftVal">Left shift by shiftVal bit</param>
    /// <returns>Left-shifted BigInteger</returns>
    public static BigInteger operator <<(BigInteger bi1, int shiftVal)
    {
        BigInteger result = new BigInteger(bi1);
        result.dataLength = shiftLeft(result.data, shiftVal);

        return result;
    }

    // least significant bits at lower part of buffer
    private static int shiftLeft(uint[] buffer, int shiftVal)
    {
        int shiftAmount = 32;
        int bufLen = buffer.Length;

        while (bufLen > 1 && buffer[bufLen - 1] == 0)
            bufLen--;

        for (int count = shiftVal; count > 0;)
        {
            if (count < shiftAmount)
                shiftAmount = count;

            ulong carry = 0;
            for (int i = 0; i < bufLen; i++)
            {
                ulong val = ((ulong)buffer[i]) << shiftAmount;
                val |= carry;

                buffer[i] = (uint)(val & 0xFFFFFFFF);
                carry = val >> 32;
            }

            if (carry != 0)
            {
                if (bufLen + 1 <= buffer.Length)
                {
                    buffer[bufLen] = (uint)carry;
                    bufLen++;
                }
            }
            count -= shiftAmount;
        }
        return bufLen;
    }


    /// <summary>
    /// Overloading of the unary &gt;&gt; operator (right shift)
    /// </summary>
    /// <remarks>
    /// Shifting by a negative number is an undefined behaviour (UB).
    /// </remarks>
    /// <param name="bi1">A BigInteger</param>
    /// <param name="shiftVal">Right shift by shiftVal bit</param>
    /// <returns>Right-shifted BigInteger</returns>
    public static BigInteger operator >>(BigInteger bi1, int shiftVal)
    {
        BigInteger result = new BigInteger(bi1);
        result.dataLength = shiftRight(result.data, shiftVal);


        if ((bi1.data[maxLength - 1] & 0x80000000) != 0) // negative
        {
            for (int i = maxLength - 1; i >= result.dataLength; i--)
                result.data[i] = 0xFFFFFFFF;

            uint mask = 0x80000000;
            for (int i = 0; i < 32; i++)
            {
                if ((result.data[result.dataLength - 1] & mask) != 0)
                    break;

                result.data[result.dataLength - 1] |= mask;
                mask >>= 1;
            }
            result.dataLength = maxLength;
        }

        return result;
    }


    private static int shiftRight(uint[] buffer, int shiftVal)
    {
        int shiftAmount = 32;
        int invShift = 0;
        int bufLen = buffer.Length;

        while (bufLen > 1 && buffer[bufLen - 1] == 0)
            bufLen--;

        for (int count = shiftVal; count > 0;)
        {
            if (count < shiftAmount)
            {
                shiftAmount = count;
                invShift = 32 - shiftAmount;
            }

            ulong carry = 0;
            for (int i = bufLen - 1; i >= 0; i--)
            {
                ulong val = ((ulong)buffer[i]) >> shiftAmount;
                val |= carry;

                carry = (((ulong)buffer[i]) << invShift) & 0xFFFFFFFF;
                buffer[i] = (uint)(val);
            }

            count -= shiftAmount;
        }

        while (bufLen > 1 && buffer[bufLen - 1] == 0)
            bufLen--;

        return bufLen;
    }


    /// <summary>
    /// Overloading of the bit-wise NOT operator (1's complement)
    /// </summary>
    /// <param name="bi1">A BigInteger</param>
    /// <returns>Complemented BigInteger</returns>
    public static BigInteger operator ~(BigInteger bi1)
    {
        BigInteger result = new BigInteger(bi1);

        for (int i = 0; i < maxLength; i++)
            result.data[i] = (uint)(~(bi1.data[i]));

        result.dataLength = maxLength;

        while (result.dataLength > 1 && result.data[result.dataLength - 1] == 0)
            result.dataLength--;

        return result;
    }


    /// <summary>
    /// Overloading of the NEGATE operator (2's complement)
    /// </summary>
    /// <param name="bi1">A BigInteger</param>
    /// <returns>Negated BigInteger or default BigInteger value if bi1 is 0</returns>
    public static BigInteger operator -(BigInteger bi1)
    {
        // handle neg of zero separately since it'll cause an overflow
        // if we proceed.

        if (bi1.dataLength == 1 && bi1.data[0] == 0)
            return (new BigInteger());

        BigInteger result = new BigInteger(bi1);

        // 1's complement
        for (int i = 0; i < maxLength; i++)
            result.data[i] = (uint)(~(bi1.data[i]));

        // add one to result of 1's complement
        long val, carry = 1;
        int index = 0;

        while (carry != 0 && index < maxLength)
        {
            val = (long)(result.data[index]);
            val++;

            result.data[index] = (uint)(val & 0xFFFFFFFF);
            carry = val >> 32;

            index++;
        }

        if ((bi1.data[maxLength - 1] & 0x80000000) == (result.data[maxLength - 1] & 0x80000000))
            throw (new ArithmeticException("Overflow in negation.\n"));

        result.dataLength = maxLength;

        while (result.dataLength > 1 && result.data[result.dataLength - 1] == 0)
            result.dataLength--;
        return result;
    }


    /// <summary>
    /// Overloading of equality operator, allows comparing 2 BigIntegers with == operator
    /// </summary>
    /// <param name="bi1">First BigInteger</param>
    /// <param name="bi2">Second BigInteger</param>
    /// <returns>Boolean result of the comparison</returns>
    public static bool operator ==(BigInteger bi1, BigInteger bi2)
    {
        return bi1.Equals(bi2);
    }


    /// <summary>
    /// Overloading of not equal operator, allows comparing 2 BigIntegers with != operator
    /// </summary>
    /// <param name="bi1">First BigInteger</param>
    /// <param name="bi2">Second BigInteger</param>
    /// <returns>Boolean result of the comparison</returns>
    public static bool operator !=(BigInteger bi1, BigInteger bi2)
    {
        return !(bi1.Equals(bi2));
    }


    /// <summary>
    /// Overriding of Equals method, allows comparing BigInteger with an arbitary object
    /// </summary>
    /// <param name="o">Input object, to be casted into BigInteger type for comparison</param>
    /// <returns>Boolean result of the comparison</returns>
    public override bool Equals(object o)
    {
        BigInteger bi = (BigInteger)o;

        if (this.dataLength != bi.dataLength)
            return false;

        for (int i = 0; i < this.dataLength; i++)
        {
            if (this.data[i] != bi.data[i])
                return false;
        }
        return true;
    }


    public override int GetHashCode()
    {
        return this.ToString().GetHashCode();
    }


    /// <summary>
    /// Overloading of greater than operator, allows comparing 2 BigIntegers with &gt; operator
    /// </summary>
    /// <param name="bi1">First BigInteger</param>
    /// <param name="bi2">Second BigInteger</param>
    /// <returns>Boolean result of the comparison</returns>
    public static bool operator >(BigInteger bi1, BigInteger bi2)
    {
        int pos = maxLength - 1;

        // bi1 is negative, bi2 is positive
        if ((bi1.data[pos] & 0x80000000) != 0 && (bi2.data[pos] & 0x80000000) == 0)
            return false;

        // bi1 is positive, bi2 is negative
        else if ((bi1.data[pos] & 0x80000000) == 0 && (bi2.data[pos] & 0x80000000) != 0)
            return true;

        // same sign
        int len = (bi1.dataLength > bi2.dataLength) ? bi1.dataLength : bi2.dataLength;
        for (pos = len - 1; pos >= 0 && bi1.data[pos] == bi2.data[pos]; pos--) ;

        if (pos >= 0)
        {
            if (bi1.data[pos] > bi2.data[pos])
                return true;
            return false;
        }
        return false;
    }


    /// <summary>
    /// Overloading of greater than operator, allows comparing 2 BigIntegers with &lt; operator
    /// </summary>
    /// <param name="bi1">First BigInteger</param>
    /// <param name="bi2">Second BigInteger</param>
    /// <returns>Boolean result of the comparison</returns>
    public static bool operator <(BigInteger bi1, BigInteger bi2)
    {
        int pos = maxLength - 1;

        // bi1 is negative, bi2 is positive
        if ((bi1.data[pos] & 0x80000000) != 0 && (bi2.data[pos] & 0x80000000) == 0)
            return true;

        // bi1 is positive, bi2 is negative
        else if ((bi1.data[pos] & 0x80000000) == 0 && (bi2.data[pos] & 0x80000000) != 0)
            return false;

        // same sign
        int len = (bi1.dataLength > bi2.dataLength) ? bi1.dataLength : bi2.dataLength;
        for (pos = len - 1; pos >= 0 && bi1.data[pos] == bi2.data[pos]; pos--) ;

        if (pos >= 0)
        {
            if (bi1.data[pos] < bi2.data[pos])
                return true;
            return false;
        }
        return false;
    }


    /// <summary>
    /// Overloading of greater than or equal to operator, allows comparing 2 BigIntegers with &gt;= operator
    /// </summary>
    /// <param name="bi1">First BigInteger</param>
    /// <param name="bi2">Second BigInteger</param>
    /// <returns>Boolean result of the comparison</returns>
    public static bool operator >=(BigInteger bi1, BigInteger bi2)
    {
        return (bi1 == bi2 || bi1 > bi2);
    }


    /// <summary>
    /// Overloading of less than or equal to operator, allows comparing 2 BigIntegers with &lt;= operator
    /// </summary>
    /// <param name="bi1">First BigInteger</param>
    /// <param name="bi2">Second BigInteger</param>
    /// <returns>Boolean result of the comparison</returns>
    public static bool operator <=(BigInteger bi1, BigInteger bi2)
    {
        return (bi1 == bi2 || bi1 < bi2);
    }


    //***********************************************************************
    // Private function that supports the division of two numbers with
    // a divisor that has more than 1 digit.
    //
    // Algorithm taken from [1]
    //***********************************************************************
    private static void multiByteDivide(BigInteger bi1, BigInteger bi2,
                                        BigInteger outQuotient, BigInteger outRemainder)
    {
        uint[] result = new uint[maxLength];

        int remainderLen = bi1.dataLength + 1;
        uint[] remainder = new uint[remainderLen];

        uint mask = 0x80000000;
        uint val = bi2.data[bi2.dataLength - 1];
        int shift = 0, resultPos = 0;

        while (mask != 0 && (val & mask) == 0)
        {
            shift++; mask >>= 1;
        }

        for (int i = 0; i < bi1.dataLength; i++)
            remainder[i] = bi1.data[i];
        shiftLeft(remainder, shift);
        bi2 = bi2 << shift;

        int j = remainderLen - bi2.dataLength;
        int pos = remainderLen - 1;

        ulong firstDivisorByte = bi2.data[bi2.dataLength - 1];
        ulong secondDivisorByte = bi2.data[bi2.dataLength - 2];

        int divisorLen = bi2.dataLength + 1;
        uint[] dividendPart = new uint[divisorLen];

        while (j > 0)
        {
            ulong dividend = ((ulong)remainder[pos] << 32) + (ulong)remainder[pos - 1];

            ulong q_hat = dividend / firstDivisorByte;
            ulong r_hat = dividend % firstDivisorByte;

            bool done = false;
            while (!done)
            {
                done = true;

                if (q_hat == 0x100000000 ||
                   (q_hat * secondDivisorByte) > ((r_hat << 32) + remainder[pos - 2]))
                {
                    q_hat--;
                    r_hat += firstDivisorByte;

                    if (r_hat < 0x100000000)
                        done = false;
                }
            }

            for (int h = 0; h < divisorLen; h++)
                dividendPart[h] = remainder[pos - h];

            BigInteger kk = new BigInteger(dividendPart);
            BigInteger ss = bi2 * (long)q_hat;

            while (ss > kk)
            {
                q_hat--;
                ss -= bi2;
            }
            BigInteger yy = kk - ss;

            for (int h = 0; h < divisorLen; h++)
                remainder[pos - h] = yy.data[bi2.dataLength - h];

            result[resultPos++] = (uint)q_hat;

            pos--;
            j--;
        }

        outQuotient.dataLength = resultPos;
        int y = 0;
        for (int x = outQuotient.dataLength - 1; x >= 0; x--, y++)
            outQuotient.data[y] = result[x];
        for (; y < maxLength; y++)
            outQuotient.data[y] = 0;

        while (outQuotient.dataLength > 1 && outQuotient.data[outQuotient.dataLength - 1] == 0)
            outQuotient.dataLength--;

        if (outQuotient.dataLength == 0)
            outQuotient.dataLength = 1;

        outRemainder.dataLength = shiftRight(remainder, shift);

        for (y = 0; y < outRemainder.dataLength; y++)
            outRemainder.data[y] = remainder[y];
        for (; y < maxLength; y++)
            outRemainder.data[y] = 0;
    }


    //***********************************************************************
    // Private function that supports the division of two numbers with
    // a divisor that has only 1 digit.
    //***********************************************************************
    private static void singleByteDivide(BigInteger bi1, BigInteger bi2,
                                         BigInteger outQuotient, BigInteger outRemainder)
    {
        uint[] result = new uint[maxLength];
        int resultPos = 0;

        // copy dividend to reminder
        for (int i = 0; i < maxLength; i++)
            outRemainder.data[i] = bi1.data[i];
        outRemainder.dataLength = bi1.dataLength;

        while (outRemainder.dataLength > 1 && outRemainder.data[outRemainder.dataLength - 1] == 0)
            outRemainder.dataLength--;

        ulong divisor = (ulong)bi2.data[0];
        int pos = outRemainder.dataLength - 1;
        ulong dividend = (ulong)outRemainder.data[pos];

        if (dividend >= divisor)
        {
            ulong quotient = dividend / divisor;
            result[resultPos++] = (uint)quotient;

            outRemainder.data[pos] = (uint)(dividend % divisor);
        }
        pos--;

        while (pos >= 0)
        {
            dividend = ((ulong)outRemainder.data[pos + 1] << 32) + (ulong)outRemainder.data[pos];
            ulong quotient = dividend / divisor;
            result[resultPos++] = (uint)quotient;

            outRemainder.data[pos + 1] = 0;
            outRemainder.data[pos--] = (uint)(dividend % divisor);
        }

        outQuotient.dataLength = resultPos;
        int j = 0;
        for (int i = outQuotient.dataLength - 1; i >= 0; i--, j++)
            outQuotient.data[j] = result[i];
        for (; j < maxLength; j++)
            outQuotient.data[j] = 0;

        while (outQuotient.dataLength > 1 && outQuotient.data[outQuotient.dataLength - 1] == 0)
            outQuotient.dataLength--;

        if (outQuotient.dataLength == 0)
            outQuotient.dataLength = 1;

        while (outRemainder.dataLength > 1 && outRemainder.data[outRemainder.dataLength - 1] == 0)
            outRemainder.dataLength--;
    }


    /// <summary>
    /// Overloading of division operator
    /// </summary>
    /// <remarks>The dataLength of the divisor's absolute value must be less than maxLength</remarks>
    /// <param name="bi1">Dividend</param>
    /// <param name="bi2">Divisor</param>
    /// <returns>Quotient of the division</returns>
    public static BigInteger operator /(BigInteger bi1, BigInteger bi2)
    {
        BigInteger quotient = new BigInteger();
        BigInteger remainder = new BigInteger();

        int lastPos = maxLength - 1;
        bool divisorNeg = false, dividendNeg = false;

        if ((bi1.data[lastPos] & 0x80000000) != 0)     // bi1 negative
        {
            bi1 = -bi1;
            dividendNeg = true;
        }
        if ((bi2.data[lastPos] & 0x80000000) != 0)     // bi2 negative
        {
            bi2 = -bi2;
            divisorNeg = true;
        }

        if (bi1 < bi2)
        {
            return quotient;
        }

        else
        {
            if (bi2.dataLength == 1)
                singleByteDivide(bi1, bi2, quotient, remainder);
            else
                multiByteDivide(bi1, bi2, quotient, remainder);

            if (dividendNeg != divisorNeg)
                return -quotient;

            return quotient;
        }
    }


    /// <summary>
    /// Overloading of modulus operator
    /// </summary>
    /// <remarks>The dataLength of the divisor's absolute value must be less than maxLength</remarks>
    /// <param name="bi1">Dividend</param>
    /// <param name="bi2">Divisor</param>
    /// <returns>Remainder of the division</returns>
    public static BigInteger operator %(BigInteger bi1, BigInteger bi2)
    {
        BigInteger quotient = new BigInteger();
        BigInteger remainder = new BigInteger(bi1);

        int lastPos = maxLength - 1;
        bool dividendNeg = false;

        if ((bi1.data[lastPos] & 0x80000000) != 0)     // bi1 negative
        {
            bi1 = -bi1;
            dividendNeg = true;
        }
        if ((bi2.data[lastPos] & 0x80000000) != 0)     // bi2 negative
            bi2 = -bi2;

        if (bi1 < bi2)
        {
            return remainder;
        }

        else
        {
            if (bi2.dataLength == 1)
                singleByteDivide(bi1, bi2, quotient, remainder);
            else
                multiByteDivide(bi1, bi2, quotient, remainder);

            if (dividendNeg)
                return -remainder;

            return remainder;
        }
    }


    /// <summary>
    /// Overloading of bitwise AND operator
    /// </summary>
    /// <param name="bi1">First BigInteger</param>
    /// <param name="bi2">Second BigInteger</param>
    /// <returns>BigInteger result after performing &amp; operation</returns>
    public static BigInteger operator &(BigInteger bi1, BigInteger bi2)
    {
        BigInteger result = new BigInteger();

        int len = (bi1.dataLength > bi2.dataLength) ? bi1.dataLength : bi2.dataLength;

        for (int i = 0; i < len; i++)
        {
            uint sum = (uint)(bi1.data[i] & bi2.data[i]);
            result.data[i] = sum;
        }

        result.dataLength = maxLength;

        while (result.dataLength > 1 && result.data[result.dataLength - 1] == 0)
            result.dataLength--;

        return result;
    }


    /// <summary>
    /// Overloading of bitwise OR operator
    /// </summary>
    /// <param name="bi1">First BigInteger</param>
    /// <param name="bi2">Second BigInteger</param>
    /// <returns>BigInteger result after performing | operation</returns>
    public static BigInteger operator |(BigInteger bi1, BigInteger bi2)
    {
        BigInteger result = new BigInteger();

        int len = (bi1.dataLength > bi2.dataLength) ? bi1.dataLength : bi2.dataLength;

        for (int i = 0; i < len; i++)
        {
            uint sum = (uint)(bi1.data[i] | bi2.data[i]);
            result.data[i] = sum;
        }

        result.dataLength = maxLength;

        while (result.dataLength > 1 && result.data[result.dataLength - 1] == 0)
            result.dataLength--;

        return result;
    }


    /// <summary>
    /// Overloading of bitwise XOR operator
    /// </summary>
    /// <param name="bi1">First BigInteger</param>
    /// <param name="bi2">Second BigInteger</param>
    /// <returns>BigInteger result after performing ^ operation</returns>
    public static BigInteger operator ^(BigInteger bi1, BigInteger bi2)
    {
        BigInteger result = new BigInteger();

        int len = (bi1.dataLength > bi2.dataLength) ? bi1.dataLength : bi2.dataLength;

        for (int i = 0; i < len; i++)
        {
            uint sum = (uint)(bi1.data[i] ^ bi2.data[i]);
            result.data[i] = sum;
        }

        result.dataLength = maxLength;

        while (result.dataLength > 1 && result.data[result.dataLength - 1] == 0)
            result.dataLength--;

        return result;
    }


    /// <summary>
    /// Compare this and a BigInteger and find the maximum one
    /// </summary>
    /// <param name="bi">BigInteger to be compared with this</param>
    /// <returns>The bigger value of this and bi</returns>
    public BigInteger max(BigInteger bi)
    {
        if (this > bi)
            return (new BigInteger(this));
        else
            return (new BigInteger(bi));
    }


    /// <summary>
    /// Compare this and a BigInteger and find the minimum one
    /// </summary>
    /// <param name="bi">BigInteger to be compared with this</param>
    /// <returns>The smaller value of this and bi</returns>
    public BigInteger min(BigInteger bi)
    {
        if (this < bi)
            return (new BigInteger(this));
        else
            return (new BigInteger(bi));

    }


    /// <summary>
    /// Returns the absolute value
    /// </summary>
    /// <returns>Absolute value of this</returns>
    public BigInteger abs()
    {
        if ((this.data[maxLength - 1] & 0x80000000) != 0)
            return (-this);
        else
            return (new BigInteger(this));
    }


    /// <summary>
    /// Returns a string representing the BigInteger in base 10
    /// </summary>
    /// <returns>string representation of the BigInteger</returns>
    public override string ToString()
    {
        return ToString(10);
    }


    /// <summary>
    /// Returns a string representing the BigInteger in [sign][magnitude] format in the specified radix
    /// </summary>
    /// <example>If the value of BigInteger is -255 in base 10, then ToString(16) returns "-FF"</example>
    /// <param name="radix">Base</param>
    /// <returns>string representation of the BigInteger in [sign][magnitude] format</returns>
    public string ToString(int radix)
    {
        if (radix < 2 || radix > 36)
            throw (new ArgumentException("Radix must be >= 2 and <= 36"));

        string charSet = "ABCDEFGHIJKLMNOPQRSTUVWXYZ";
        string result = "";

        BigInteger a = this;

        bool negative = false;
        if ((a.data[maxLength - 1] & 0x80000000) != 0)
        {
            negative = true;
            try
            {
                a = -a;
            }
            catch (Exception) { }
        }

        BigInteger quotient = new BigInteger();
        BigInteger remainder = new BigInteger();
        BigInteger biRadix = new BigInteger(radix);

        if (a.dataLength == 1 && a.data[0] == 0)
            result = "0";
        else
        {
            while (a.dataLength > 1 || (a.dataLength == 1 && a.data[0] != 0))
            {
                singleByteDivide(a, biRadix, quotient, remainder);

                if (remainder.data[0] < 10)
                    result = remainder.data[0] + result;
                else
                    result = charSet[(int)remainder.data[0] - 10] + result;

                a = quotient;
            }
            if (negative)
                result = "-" + result;
        }

        return result;
    }


    /// <summary>
    /// Returns a hex string showing the contains of the BigInteger
    /// </summary>
    /// <example>
    /// 1) If the value of BigInteger is 255 in base 10, then ToHexString() returns "FF"
    /// 2) If the value of BigInteger is -255 in base 10, thenToHexString() returns ".....FFFFFFFFFF01", which is the 2's complement representation of -255.
    /// </example>
    /// <returns></returns>
    public string ToHexString()
    {
        string result = data[dataLength - 1].ToString("X");

        for (int i = dataLength - 2; i >= 0; i--)
        {
            result += data[i].ToString("X8");
        }

        return result;
    }


	public BigInteger Pow(BigInteger n)
	{
		BigInteger x = this;
		BigInteger result = new BigInteger(1);
		while ( n > 0 )
		{
			if ( ( n & 1 ) == 0 )
			{
				x = x * x;
				n = n >> 1;
			}
			else
			{
				result = result * x;
				n = n - 1;
			}
		}
		return result;
	}

    /// <summary>
    /// Modulo Exponentiation
    /// </summary>
    /// <param name="exp">Exponential</param>
    /// <param name="n">Modulo</param>
    /// <returns>BigInteger result of raising this to the power of exp and then modulo n </returns>
    public BigInteger modPow(BigInteger exp, BigInteger n)
    {
        if ((exp.data[maxLength - 1] & 0x80000000) != 0)
            throw (new ArithmeticException("Positive exponents only."));

        BigInteger resultNum = 1;
        BigInteger tempNum;
        bool thisNegative = false;

        if ((this.data[maxLength - 1] & 0x80000000) != 0)   // negative this
        {
            tempNum = -this % n;
            thisNegative = true;
        }
        else
            tempNum = this % n;  // ensures (tempNum * tempNum) < b^(2k)

        if ((n.data[maxLength - 1] & 0x80000000) != 0)   // negative n
            n = -n;

        // calculate constant = b^(2k) / m
        BigInteger constant = new BigInteger();

        int i = n.dataLength << 1;
        constant.data[i] = 0x00000001;
        constant.dataLength = i + 1;

        constant = constant / n;
        int totalBits = exp.bitCount();
        int count = 0;

        // perform squaring and multiply exponentiation
        for (int pos = 0; pos < exp.dataLength; pos++)
        {
            uint mask = 0x01;

            for (int index = 0; index < 32; index++)
            {
                if ((exp.data[pos] & mask) != 0)
                    resultNum = BarrettReduction(resultNum * tempNum, n, constant);

                mask <<= 1;

                tempNum = BarrettReduction(tempNum * tempNum, n, constant);


                if (tempNum.dataLength == 1 && tempNum.data[0] == 1)
                {
                    if (thisNegative && (exp.data[0] & 0x1) != 0)    //odd exp
                        return -resultNum;
                    return resultNum;
                }
                count++;
                if (count == totalBits)
                    break;
            }
        }

        if (thisNegative && (exp.data[0] & 0x1) != 0)    //odd exp
            return -resultNum;

        return resultNum;
    }


    /// <summary>
    /// Fast calculation of modular reduction using Barrett's reduction
    /// </summary>
    /// <remarks>
    /// Requires x &lt; b^(2k), where b is the base.  In this case, base is 2^32 (uint).
    ///
    /// Reference [4]
    /// </remarks>
    /// <param name="x"></param>
    /// <param name="n"></param>
    /// <param name="constant"></param>
    /// <returns></returns>
    private BigInteger BarrettReduction(BigInteger x, BigInteger n, BigInteger constant)
    {
        int k = n.dataLength,
            kPlusOne = k + 1,
            kMinusOne = k - 1;

        BigInteger q1 = new BigInteger();

        // q1 = x / b^(k-1)
        for (int i = kMinusOne, j = 0; i < x.dataLength; i++, j++)
            q1.data[j] = x.data[i];
        q1.dataLength = x.dataLength - kMinusOne;
        if (q1.dataLength <= 0)
            q1.dataLength = 1;


        BigInteger q2 = q1 * constant;
        BigInteger q3 = new BigInteger();

        // q3 = q2 / b^(k+1)
        for (int i = kPlusOne, j = 0; i < q2.dataLength; i++, j++)
            q3.data[j] = q2.data[i];
        q3.dataLength = q2.dataLength - kPlusOne;
        if (q3.dataLength <= 0)
            q3.dataLength = 1;


        // r1 = x mod b^(k+1)
        // i.e. keep the lowest (k+1) words
        BigInteger r1 = new BigInteger();
        int lengthToCopy = (x.dataLength > kPlusOne) ? kPlusOne : x.dataLength;
        for (int i = 0; i < lengthToCopy; i++)
            r1.data[i] = x.data[i];
        r1.dataLength = lengthToCopy;


        // r2 = (q3 * n) mod b^(k+1)
        // partial multiplication of q3 and n

        BigInteger r2 = new BigInteger();
        for (int i = 0; i < q3.dataLength; i++)
        {
            if (q3.data[i] == 0) continue;

            ulong mcarry = 0;
            int t = i;
            for (int j = 0; j < n.dataLength && t < kPlusOne; j++, t++)
            {
                // t = i + j
                ulong val = ((ulong)q3.data[i] * (ulong)n.data[j]) +
                             (ulong)r2.data[t] + mcarry;

                r2.data[t] = (uint)(val & 0xFFFFFFFF);
                mcarry = (val >> 32);
            }

            if (t < kPlusOne)
                r2.data[t] = (uint)mcarry;
        }
        r2.dataLength = kPlusOne;
        while (r2.dataLength > 1 && r2.data[r2.dataLength - 1] == 0)
            r2.dataLength--;

        r1 -= r2;
        if ((r1.data[maxLength - 1] & 0x80000000) != 0)        // negative
        {
            BigInteger val = new BigInteger();
            val.data[kPlusOne] = 0x00000001;
            val.dataLength = kPlusOne + 1;
            r1 += val;
        }

        while (r1 >= n)
            r1 -= n;

        return r1;
    }


    /// <summary>
    /// Returns gcd(this, bi)
    /// </summary>
    /// <param name="bi"></param>
    /// <returns>Greatest Common Divisor of this and bi</returns>
    public BigInteger gcd(BigInteger bi)
    {
        BigInteger x;
        BigInteger y;

        if ((data[maxLength - 1] & 0x80000000) != 0)     // negative
            x = -this;
        else
            x = this;

        if ((bi.data[maxLength - 1] & 0x80000000) != 0)     // negative
            y = -bi;
        else
            y = bi;

        BigInteger g = y;

        while (x.dataLength > 1 || (x.dataLength == 1 && x.data[0] != 0))
        {
            g = x;
            x = y % x;
            y = g;
        }

        return g;
    }
	
    /// <summary>
    /// Returns lcm(this, bi) = ( (|this*bi|) / gcd(this, bi) )
    /// </summary>
    /// <param name="bi"></param>
    /// <returns>Largest Common Multiplier of this and bi</returns>
    public BigInteger lcm(BigInteger bi)
    {
        BigInteger x;
        BigInteger y;

        if ((data[maxLength - 1] & 0x80000000) != 0)    	// negative
            x = -this;
        else
            x = this;

        if ((bi.data[maxLength - 1] & 0x80000000) != 0)     // negative
            y = -bi;
        else
            y = bi;

        return ((x*y) / x.gcd(y));
    }


    /// <summary>
    /// Populates "this" with the specified amount of random bits
    /// </summary>
    /// <param name="bits"></param>
    /// <param name="rand"></param>
    public void genRandomBits(int bits, Random rand)
    {
        int dwords = bits >> 5;
        int remBits = bits & 0x1F;

        if (remBits != 0)
            dwords++;

        if (dwords > maxLength || bits <= 0)
            throw (new ArithmeticException("Number of required bits is not valid."));

        byte[] randBytes = new byte[dwords * 4];
        rand.NextBytes(randBytes);

        for (int i = 0; i < dwords; i++)
            data[i] = BitConverter.ToUInt32(randBytes, i * 4);
        
        for (int i = dwords; i < maxLength; i++)
            data[i] = 0;

        if (remBits != 0)
        {
            uint mask;

            if (bits != 1)
            {
                mask = (uint)(0x01 << (remBits - 1));
                data[dwords - 1] |= mask;
            }

            mask = (uint)(0xFFFFFFFF >> (32 - remBits));
            data[dwords - 1] &= mask;
        }
        else
            data[dwords - 1] |= 0x80000000;

        dataLength = dwords;

        if (dataLength == 0)
            dataLength = 1;
    }


    /// <summary>
    /// Populates "this" with the specified amount of random bits (secured version)
    /// </summary>
    /// <param name="bits"></param>
    /// <param name="rng"></param>
    public void genRandomBits(int bits, RNGCryptoServiceProvider rng)
    {
        int dwords = bits >> 5;
        int remBits = bits & 0x1F;

        if (remBits != 0)
            dwords++;

        if (dwords > maxLength || bits <= 0)
            throw (new ArithmeticException("Number of required bits is not valid."));

        byte[] randomBytes = new byte[dwords * 4];
        rng.GetBytes(randomBytes);

        for (int i = 0; i < dwords; i++)
            data[i] = BitConverter.ToUInt32(randomBytes, i * 4);

        for (int i = dwords; i < maxLength; i++)
            data[i] = 0;

        if (remBits != 0)
        {
            uint mask;

            if (bits != 1)
            {
                mask = (uint)(0x01 << (remBits - 1));
                data[dwords - 1] |= mask;
            }

            mask = (uint)(0xFFFFFFFF >> (32 - remBits));
            data[dwords - 1] &= mask;
        }
        else
            data[dwords - 1] |= 0x80000000;

        dataLength = dwords;

        if (dataLength == 0)
            dataLength = 1;
    }


    /// <summary>
    /// Returns the position of the most significant bit in the BigInteger
    /// </summary>
    /// <example>
    /// 1) The result is 1, if the value of BigInteger is 0...0000 0000
    /// 2) The result is 1, if the value of BigInteger is 0...0000 0001
    /// 3) The result is 2, if the value of BigInteger is 0...0000 0010
    /// 4) The result is 2, if the value of BigInteger is 0...0000 0011
    /// 5) The result is 5, if the value of BigInteger is 0...0001 0011
    /// </example>
    /// <returns></returns>
    public int bitCount()
    {
        while (dataLength > 1 && data[dataLength - 1] == 0)
            dataLength--;

        uint value = data[dataLength - 1];
        uint mask = 0x80000000;
        int bits = 32;

        while (bits > 0 && (value & mask) == 0)
        {
            bits--;
            mask >>= 1;
        }
        bits += ((dataLength - 1) << 5);

        return bits == 0 ? 1 : bits;
    }


    /// <summary>
    /// Probabilistic prime test based on Fermat's little theorem
    /// </summary>
    /// <remarks>
    /// for any a &lt; p (p does not divide a) if
    ///      a^(p-1) mod p != 1 then p is not prime.
    ///
    /// Otherwise, p is probably prime (pseudoprime to the chosen base).
    /// 
    /// This method is fast but fails for Carmichael numbers when the randomly chosen base is a factor of the number.
    /// </remarks>
    /// <param name="confidence">Number of chosen bases</param>
    /// <returns>True if this is a pseudoprime to randomly chosen bases</returns>
    public bool FermatLittleTest(int confidence)
    {
        BigInteger thisVal;
        if ((this.data[maxLength - 1] & 0x80000000) != 0)        // negative
            thisVal = -this;
        else
            thisVal = this;

        if (thisVal.dataLength == 1)
        {
            // test small numbers
            if (thisVal.data[0] == 0 || thisVal.data[0] == 1)
                return false;
            else if (thisVal.data[0] == 2 || thisVal.data[0] == 3)
                return true;
        }

        if ((thisVal.data[0] & 0x1) == 0)     // even numbers
            return false;

        int bits = thisVal.bitCount();
        BigInteger a = new BigInteger();
        BigInteger p_sub1 = thisVal - (new BigInteger(1));
        Random rand = new Random();

        for (int round = 0; round < confidence; round++)
        {
            bool done = false;

            while (!done)		// generate a < n
            {
                int testBits = 0;

                // make sure "a" has at least 2 bits
                while (testBits < 2)
                    testBits = (int)(rand.NextDouble() * bits);

                a.genRandomBits(testBits, rand);

                int byteLen = a.dataLength;

                // make sure "a" is not 0
                if (byteLen > 1 || (byteLen == 1 && a.data[0] != 1))
                    done = true;
            }

            // check whether a factor exists (fix for version 1.03)
            BigInteger gcdTest = a.gcd(thisVal);
            if (gcdTest.dataLength == 1 && gcdTest.data[0] != 1)
                return false;

            // calculate a^(p-1) mod p
            BigInteger expResult = a.modPow(p_sub1, thisVal);

            int resultLen = expResult.dataLength;

            // is NOT prime is a^(p-1) mod p != 1

            if (resultLen > 1 || (resultLen == 1 && expResult.data[0] != 1))
                return false;
        }

        return true;
    }


    /// <summary>
    /// Probabilistic prime test based on Rabin-Miller's
    /// </summary>
    /// <remarks>
    /// for any p &gt; 0 with p - 1 = 2^s * t
    ///
    /// p is probably prime (strong pseudoprime) if for any a &lt; p,
    /// 1) a^t mod p = 1 or
    /// 2) a^((2^j)*t) mod p = p-1 for some 0 &lt;= j &lt;= s-1
    ///
    /// Otherwise, p is composite.
    /// </remarks>
    /// <param name="confidence">Number of chosen bases</param>
    /// <returns>True if this is a strong pseudoprime to randomly chosen bases</returns>
    public bool RabinMillerTest(int confidence)
    {
        BigInteger thisVal;
        if ((this.data[maxLength - 1] & 0x80000000) != 0)        // negative
            thisVal = -this;
        else
            thisVal = this;

        if (thisVal.dataLength == 1)
        {
            // test small numbers
            if (thisVal.data[0] == 0 || thisVal.data[0] == 1)
                return false;
            else if (thisVal.data[0] == 2 || thisVal.data[0] == 3)
                return true;
        }

        if ((thisVal.data[0] & 0x1) == 0)     // even numbers
            return false;


        // calculate values of s and t
        BigInteger p_sub1 = thisVal - (new BigInteger(1));
        int s = 0;

        for (int index = 0; index < p_sub1.dataLength; index++)
        {
            uint mask = 0x01;

            for (int i = 0; i < 32; i++)
            {
                if ((p_sub1.data[index] & mask) != 0)
                {
                    index = p_sub1.dataLength;      // to break the outer loop
                    break;
                }
                mask <<= 1;
                s++;
            }
        }

        BigInteger t = p_sub1 >> s;

        int bits = thisVal.bitCount();
        BigInteger a = new BigInteger();
        Random rand = new Random();

        for (int round = 0; round < confidence; round++)
        {
            bool done = false;

            while (!done)		// generate a < n
            {
                int testBits = 0;

                // make sure "a" has at least 2 bits
                while (testBits < 2)
                    testBits = (int)(rand.NextDouble() * bits);

                a.genRandomBits(testBits, rand);

                int byteLen = a.dataLength;

                // make sure "a" is not 0
                if (byteLen > 1 || (byteLen == 1 && a.data[0] != 1))
                    done = true;
            }

            // check whether a factor exists (fix for version 1.03)
            BigInteger gcdTest = a.gcd(thisVal);
            if (gcdTest.dataLength == 1 && gcdTest.data[0] != 1)
                return false;

            BigInteger b = a.modPow(t, thisVal);

            bool result = false;

            if (b.dataLength == 1 && b.data[0] == 1)         // a^t mod p = 1
                result = true;

            for (int j = 0; result == false && j < s; j++)
            {
                if (b == p_sub1)         // a^((2^j)*t) mod p = p-1 for some 0 <= j <= s-1
                {
                    result = true;
                    break;
                }

                b = (b * b) % thisVal;
            }

            if (result == false)
                return false;
        }
        return true;
    }


    /// <summary>
    /// Probabilistic prime test based on Solovay-Strassen (Euler Criterion)
    /// </summary>
    /// <remarks>
    ///  p is probably prime if for any a &lt; p (a is not multiple of p),
    /// a^((p-1)/2) mod p = J(a, p)
    ///
    /// where J is the Jacobi symbol.
    ///
    /// Otherwise, p is composite.
    /// </remarks>
    /// <param name="confidence">Number of chosen bases</param>
    /// <returns>True if this is a Euler pseudoprime to randomly chosen bases</returns>
    public bool SolovayStrassenTest(int confidence)
    {
        BigInteger thisVal;
        if ((this.data[maxLength - 1] & 0x80000000) != 0)        // negative
            thisVal = -this;
        else
            thisVal = this;

        if (thisVal.dataLength == 1)
        {
            // test small numbers
            if (thisVal.data[0] == 0 || thisVal.data[0] == 1)
                return false;
            else if (thisVal.data[0] == 2 || thisVal.data[0] == 3)
                return true;
        }

        if ((thisVal.data[0] & 0x1) == 0)     // even numbers
            return false;


        int bits = thisVal.bitCount();
        BigInteger a = new BigInteger();
        BigInteger p_sub1 = thisVal - 1;
        BigInteger p_sub1_shift = p_sub1 >> 1;

        Random rand = new Random();

        for (int round = 0; round < confidence; round++)
        {
            bool done = false;

            while (!done)		// generate a < n
            {
                int testBits = 0;

                // make sure "a" has at least 2 bits
                while (testBits < 2)
                    testBits = (int)(rand.NextDouble() * bits);

                a.genRandomBits(testBits, rand);

                int byteLen = a.dataLength;

                // make sure "a" is not 0
                if (byteLen > 1 || (byteLen == 1 && a.data[0] != 1))
                    done = true;
            }

            // check whether a factor exists (fix for version 1.03)
            BigInteger gcdTest = a.gcd(thisVal);
            if (gcdTest.dataLength == 1 && gcdTest.data[0] != 1)
                return false;

            // calculate a^((p-1)/2) mod p

            BigInteger expResult = a.modPow(p_sub1_shift, thisVal);
            if (expResult == p_sub1)
                expResult = -1;

            // calculate Jacobi symbol
            BigInteger jacob = Jacobi(a, thisVal);

            // if they are different then it is not prime
            if (expResult != jacob)
                return false;
        }

        return true;
    }


    /// <summary>
    /// Implementation of the Lucas Strong Pseudo Prime test
    /// </summary>
    /// <remarks>
    /// Let n be an odd number with gcd(n,D) = 1, and n - J(D, n) = 2^s * d
    /// with d odd and s >= 0.
    ///
    /// If Ud mod n = 0 or V2^r*d mod n = 0 for some 0 &lt;= r &lt; s, then n
    /// is a strong Lucas pseudoprime with parameters (P, Q).  We select
    /// P and Q based on Selfridge.
    /// </remarks>
    /// <returns>True if number is a strong Lucus pseudo prime</returns>
    public bool LucasStrongTest()
    {
        BigInteger thisVal;
        if ((this.data[maxLength - 1] & 0x80000000) != 0)        // negative
            thisVal = -this;
        else
            thisVal = this;

        if (thisVal.dataLength == 1)
        {
            // test small numbers
            if (thisVal.data[0] == 0 || thisVal.data[0] == 1)
                return false;
            else if (thisVal.data[0] == 2 || thisVal.data[0] == 3)
                return true;
        }

        if ((thisVal.data[0] & 0x1) == 0)     // even numbers
            return false;

        return LucasStrongTestHelper(thisVal);
    }


    private bool LucasStrongTestHelper(BigInteger thisVal)
    {
        // Do the test (selects D based on Selfridge)
        // Let D be the first element of the sequence
        // 5, -7, 9, -11, 13, ... for which J(D,n) = -1
        // Let P = 1, Q = (1-D) / 4

        long D = 5, sign = -1, dCount = 0;
        bool done = false;

        while (!done)
        {
            int Jresult = BigInteger.Jacobi(D, thisVal);

            if (Jresult == -1)
                done = true;    // J(D, this) = 1
            else
            {
                if (Jresult == 0 && Math.Abs(D) < thisVal)       // divisor found
                    return false;

                if (dCount == 20)
                {
                    // check for square
                    BigInteger root = thisVal.sqrt();
                    if (root * root == thisVal)
                        return false;
                }

                D = (Math.Abs(D) + 2) * sign;
                sign = -sign;
            }
            dCount++;
        }

        long Q = (1 - D) >> 2;

        BigInteger p_add1 = thisVal + 1;
        int s = 0;

        for (int index = 0; index < p_add1.dataLength; index++)
        {
            uint mask = 0x01;

            for (int i = 0; i < 32; i++)
            {
                if ((p_add1.data[index] & mask) != 0)
                {
                    index = p_add1.dataLength;      // to break the outer loop
                    break;
                }
                mask <<= 1;
                s++;
            }
        }

        BigInteger t = p_add1 >> s;

        // calculate constant = b^(2k) / m
        // for Barrett Reduction
        BigInteger constant = new BigInteger();

        int nLen = thisVal.dataLength << 1;
        constant.data[nLen] = 0x00000001;
        constant.dataLength = nLen + 1;

        constant = constant / thisVal;

        BigInteger[] lucas = LucasSequenceHelper(1, Q, t, thisVal, constant, 0);
        bool isPrime = false;

        if ((lucas[0].dataLength == 1 && lucas[0].data[0] == 0) ||
           (lucas[1].dataLength == 1 && lucas[1].data[0] == 0))
        {
            // u(t) = 0 or V(t) = 0
            isPrime = true;
        }

        for (int i = 1; i < s; i++)
        {
            if (!isPrime)
            {
                // doubling of index
                lucas[1] = thisVal.BarrettReduction(lucas[1] * lucas[1], thisVal, constant);
                lucas[1] = (lucas[1] - (lucas[2] << 1)) % thisVal;

                if ((lucas[1].dataLength == 1 && lucas[1].data[0] == 0))
                    isPrime = true;
            }

            lucas[2] = thisVal.BarrettReduction(lucas[2] * lucas[2], thisVal, constant);     //Q^k
        }


        if (isPrime)     // additional checks for composite numbers
        {
            // If n is prime and gcd(n, Q) == 1, then
            // Q^((n+1)/2) = Q * Q^((n-1)/2) is congruent to (Q * J(Q, n)) mod n

            BigInteger g = thisVal.gcd(Q);
            if (g.dataLength == 1 && g.data[0] == 1)         // gcd(this, Q) == 1
            {
                if ((lucas[2].data[maxLength - 1] & 0x80000000) != 0)
                    lucas[2] += thisVal;

                BigInteger temp = (Q * BigInteger.Jacobi(Q, thisVal)) % thisVal;
                if ((temp.data[maxLength - 1] & 0x80000000) != 0)
                    temp += thisVal;

                if (lucas[2] != temp)
                    isPrime = false;
            }
        }

        return isPrime;
    }


    /// <summary>
    /// Determines whether a number is probably prime using the Rabin-Miller's test
    /// </summary>
    /// <remarks>
    /// Before applying the test, the number is tested for divisibility by primes &lt; 2000
    /// </remarks>
    /// <param name="confidence">Number of chosen bases</param>
    /// <returns>True if this is probably prime</returns>
    public bool isProbablePrime(int confidence)
    {
        BigInteger thisVal;
        if ((this.data[maxLength - 1] & 0x80000000) != 0)        // negative
            thisVal = -this;
        else
            thisVal = this;

        // test for divisibility by primes < 2000
        for (int p = 0; p < primesBelow2000.Length; p++)
        {
            BigInteger divisor = primesBelow2000[p];

            if (divisor >= thisVal)
                break;

            BigInteger resultNum = thisVal % divisor;
            if (resultNum.IntValue() == 0)
                return false;
        }

        if (thisVal.RabinMillerTest(confidence))
            return true;
        else
            return false;
    }


    /// <summary>
    /// Determines whether this BigInteger is probably prime using a combination of base 2 strong pseudoprime test and Lucas strong pseudoprime test 
    /// </summary>
    /// <remarks>
    /// The sequence of the primality test is as follows,
    ///
    /// 1) Trial divisions are carried out using prime numbers below 2000.
    ///    if any of the primes divides this BigInteger, then it is not prime.
    ///
    /// 2) Perform base 2 strong pseudoprime test.  If this BigInteger is a
    ///    base 2 strong pseudoprime, proceed on to the next step.
    ///
    /// 3) Perform strong Lucas pseudoprime test.
    /// 
    /// For a detailed discussion of this primality test, see [6].
    /// </remarks>
    /// <returns>True if this is probably prime</returns>
    public bool isProbablePrime()
    {
        BigInteger thisVal;
        if ((this.data[maxLength - 1] & 0x80000000) != 0)        // negative
            thisVal = -this;
        else
            thisVal = this;

        if (thisVal.dataLength == 1)
        {
            // test small numbers
            if (thisVal.data[0] == 0 || thisVal.data[0] == 1)
                return false;
            else if (thisVal.data[0] == 2 || thisVal.data[0] == 3)
                return true;
        }

        if ((thisVal.data[0] & 0x1) == 0)     // even numbers
            return false;


        // test for divisibility by primes < 2000
        for (int p = 0; p < primesBelow2000.Length; p++)
        {
            BigInteger divisor = primesBelow2000[p];

            if (divisor >= thisVal)
                break;

            BigInteger resultNum = thisVal % divisor;
            if (resultNum.IntValue() == 0)
                return false;
        }

        // Perform BASE 2 Rabin-Miller Test

        // calculate values of s and t
        BigInteger p_sub1 = thisVal - (new BigInteger(1));
        int s = 0;

        for (int index = 0; index < p_sub1.dataLength; index++)
        {
            uint mask = 0x01;

            for (int i = 0; i < 32; i++)
            {
                if ((p_sub1.data[index] & mask) != 0)
                {
                    index = p_sub1.dataLength;      // to break the outer loop
                    break;
                }
                mask <<= 1;
                s++;
            }
        }

        BigInteger t = p_sub1 >> s;

        int bits = thisVal.bitCount();
        BigInteger a = 2;

        // b = a^t mod p
        BigInteger b = a.modPow(t, thisVal);
        bool result = false;

        if (b.dataLength == 1 && b.data[0] == 1)         // a^t mod p = 1
            result = true;

        for (int j = 0; result == false && j < s; j++)
        {
            if (b == p_sub1)         // a^((2^j)*t) mod p = p-1 for some 0 <= j <= s-1
            {
                result = true;
                break;
            }

            b = (b * b) % thisVal;
        }

        // if number is strong pseudoprime to base 2, then do a strong lucas test
        if (result)
            result = LucasStrongTestHelper(thisVal);

        return result;
    }


    /// <summary>
    /// Returns the lowest 4 bytes of the BigInteger as an int
    /// </summary>
    /// <returns>Lowest 4 bytes as integer</returns>
    public int IntValue()
    {
        return (int)data[0];
    }


    /// <summary>
    /// Returns the lowest 8 bytes of the BigInteger as a long
    /// </summary>
    /// <returns>Lowest 8 bytes as long</returns>
    public long LongValue()
    {
        long val = 0;

        val = (long)data[0];
        try
        {       // exception if maxLength = 1
            val |= (long)data[1] << 32;
        }
        catch (Exception)
        {
            if ((data[0] & 0x80000000) != 0) // negative
                val = (int)data[0];
        }

        return val;
    }


    /// <summary>
    /// Computes the Jacobi Symbol for 2 BigInteger a and b
    /// </summary>
    /// <remarks>
    /// Algorithm adapted from [3] and [4] with some optimizations
    /// </remarks>
    /// <param name="a">Any BigInteger</param>
    /// <param name="b">Odd BigInteger</param>
    /// <returns>Jacobi Symbol</returns>
    public static int Jacobi(BigInteger a, BigInteger b)
    {
        // Jacobi defined only for odd integers
        if ((b.data[0] & 0x1) == 0)
            throw (new ArgumentException("Jacobi defined only for odd integers."));

        if (a >= b) a %= b;
        if (a.dataLength == 1 && a.data[0] == 0) return 0;  // a == 0
        if (a.dataLength == 1 && a.data[0] == 1) return 1;  // a == 1

        if (a < 0)
        {
            if ((((b - 1).data[0]) & 0x2) == 0)       //if( (((b-1) >> 1).data[0] & 0x1) == 0)
                return Jacobi(-a, b);
            else
                return -Jacobi(-a, b);
        }

        int e = 0;
        for (int index = 0; index < a.dataLength; index++)
        {
            uint mask = 0x01;

            for (int i = 0; i < 32; i++)
            {
                if ((a.data[index] & mask) != 0)
                {
                    index = a.dataLength;      // to break the outer loop
                    break;
                }
                mask <<= 1;
                e++;
            }
        }

        BigInteger a1 = a >> e;

        int s = 1;
        if ((e & 0x1) != 0 && ((b.data[0] & 0x7) == 3 || (b.data[0] & 0x7) == 5))
            s = -1;

        if ((b.data[0] & 0x3) == 3 && (a1.data[0] & 0x3) == 3)
            s = -s;

        if (a1.dataLength == 1 && a1.data[0] == 1)
            return s;
        else
            return (s * Jacobi(b % a1, a1));
    }


    /// <summary>
    /// Generates a positive BigInteger that is probably prime
    /// </summary>
    /// <param name="bits">Number of bit</param>
    /// <param name="confidence">Number of chosen bases</param>
    /// <param name="rand">Random object</param>
    /// <returns>A probably prime number</returns>
    public static BigInteger genPseudoPrime(int bits, int confidence, Random rand)
    {
        BigInteger result = new BigInteger();
        bool done = false;

        while (!done)
        {
            result.genRandomBits(bits, rand);
            result.data[0] |= 0x01;		// make it odd

            // prime test
            done = result.isProbablePrime(confidence);
        }
        return result;
    }


    /// <summary>
    /// Generates a positive BigInteger that is probably prime (secured version)
    /// </summary>
    /// <param name="bits">Number of bit</param>
    /// <param name="confidence">Number of chosen bases</param>
    /// <param name="rand">RNGCryptoServiceProvider object</param>
    /// <returns>A probably prime number</returns>
    public static BigInteger genPseudoPrime(int bits, int confidence, RNGCryptoServiceProvider rand)
    {
        BigInteger result = new BigInteger();
        bool done = false;

        while (!done)
        {
            result.genRandomBits(bits, rand);
            result.data[0] |= 0x01;		// make it odd

            // prime test
            done = result.isProbablePrime(confidence);
        }
        return result;
    }


    public BigInteger prevprime(int confidence = 10)
    {
		BigInteger big = this;
		big = ( big - ( (big % 2 == 0) ? 1 : 2 ) );
		bool isprime = big.isProbablePrime(confidence);
		
		while(isprime==false){
            big = (big - 2);
            isprime = big.isProbablePrime(confidence);
        }
//		log("return prevprime: "+big);
        return big;
    }


    public BigInteger nextprime(int confidence = 10)
    {
		BigInteger big = this;
		big = ( big + ( (big % 2 == 0) ? 1 : 2 ) );
		bool isprime = big.isProbablePrime(confidence);
		
		while(isprime==false){
            big = (big + 2);
            isprime = big.isProbablePrime(confidence);
        }
		
        return big;
	}


    public bool isSafePrime(int confidence = 10){				//is the prime, value of (p-1)/2, where p = this? (true/false)			
		return (
						this.isProbablePrime(confidence)
					&&	(
							(this-1) / 2
						)
						.isProbablePrime(confidence)
				)
		;
	}


	// Generate Safe Prime
    public static BigInteger genSafePrime(
		int bits
	,	int confidence = 10
	,	string mode = "previous"
	,	BigInteger number = null
	,	Random rand = null
	)
    {
		if(object.ReferenceEquals(null, number)){number = new BigInteger();}
		if(object.ReferenceEquals(null, rand)){rand = new Random();}
		
		//	Proof of the validity of the representation a Safe-Prime number, in form: p = 12*k - 1:
		//
		//	Let q = 12*x+r; where x - natural number, r = q%12 - remainder by modulo 12, and number with value from 0 up to 11 (0,1,2,3,4,5,6,7,8,9,10,11).
		//	In this form can be represented each natural number.
		//
		//	Now, let us prove that the representation of Safe-Prime, in form q = 12*x+11:
		//
		//	1.	When r is even, r = 2*y; q = 12*x + r = 12*x + 2y; q = 2*(6x+y) - so q have divisor 2, and this is even number, not an odd prime number.
		//		So, y = 0,1,2,3,4,5, r = 0,2,4,6,8,10 - excluded.
		//	
		//	2. Now, exclude an odd r:
		//		When r = 1; q = 12*x + 1; (q-1)/2 = 12*x/2 = 6*x = 2*3x - have divisor 2, and this is even number, not an odd Sophie-Germen prime number.
		//		When r = 3; q = 12*x + 3; q = 3*(4x+1) - have divisor 3, and this is not a prime, because this have no divisors besides 1 and itself.
		//		When r = 5; q = 12*x + 5; (q-1)/2 = (12*x+4)/2 = 2*(6x+2)/2 = (6x+2) = 2*(3x+1) - have divisor 2, and this is even number, not an odd Sophie-Germen prime number.
		//			Exception: x = 0; q = 12*0 + 5 = 5; (q-1)/2 = (5-1)/2 = 4/2 = 2, is even, but this is a Sophie-Germen prime-number, and this have divisor 1 and itself.
		//		When r = 7; q = 12*x + 7; (q-1)/2 = (12*x+6)/2 = 2*(6x+3)/2 = (6x+3) = 3*(2x+1) - have divisor 3, and this is not a prime, because this have no divisors besides 1 and itself.
		//			Exception: x = 0; q = 12*0 + 7 = 7; (q-1)/2 = (7-1)/2 = 6/2 = 3, have divisor 3, but this is a Sophie-Germen prime-number, and this have divisor 1 and itself.
		//		When r = 9; q = 12*x + 9; (q-1)/2 = (12*x+8)/2 = 2*(6*x+4)/2 = (6x+4) = 2*(3x+2) - have divisor 2, and this is even number, not an odd Sophie-Germen prime number.
		//
		//	After this all, from all possible values of r = q%12, from the numbers 0,1,2,3,4,5,6,7,8,9,10,11,
		//	was been excluded (two exceptions) the values r = 0,2,4,6,8,10,1,3,5,7,9 (sorted: 0,1,2,3,4,5,6,7,8,9,10), and only one option remains - value 11.
		//	Consequently, r = 11, and any Safe-Prime nubmer (except for 5, 7), can be represented in form q = 12*x + 11;
		//	Now, let, k = (x+1); q = 12*(x+1) - 1 = 12k - 1; Consequently, q = 12k - 1.
		//	
		//	Original statement is proven.
	
		if(!(number == new BigInteger()) && number.isSafePrime()){return number;}
		
		BigInteger p = new BigInteger();
		BigInteger prime = new BigInteger();
		if(number == new BigInteger()){
			prime.genRandomBits(bits, rand);
		}else{
			prime = number;
		}
		
		prime = (
					(prime.isProbablePrime(confidence))									//if already prime
						? prime															//use it
						: prime.prevprime()
				)
		;
		
//		return new BigInteger(0);	//temp test...
		
		prime = (																		//find next or previous prime, (12k - 1)
							(!mode.Contains("prev"))
								? ( ( prime - ( prime % 12 ) + 12 ) - 1 )	//	((p - (p%12) + 12) - 1) 	->	next number			(12k - 1)
								: ( prime - ( prime % 12 ) - 1 )			//	(p - (p%12) - 1) 			-> 	previous number		(12k - 1)
				)
		;

		do{
			prime = ( (mode.Contains("prev")) ? (prime-12) : (prime+12) );	//next or previous nubmer (12k-1)
			//find next prime p, by rolling, using MillerRabin() primality check
			p = (
					( mode.Contains("doubled"))
						? ((prime*2)+1)					//make p*2+1
						: (prime-1)/2						//or (p-1)/2
				)
			;
		}while(
				(prime>0)
			&&	(
					(!prime.isProbablePrime(confidence))		//check primality for prime
				||	(!p.isProbablePrime(confidence))			//and p
			)
		);
		p = ( ( mode.Contains( "doubled" ) ) ? p : prime );	//return safe prime, if next or previous was been Sofi-Germen prime, and need to return doubled Safe-prime.
		
		return p;									//return a safe prime
    }


	public static bool isStrongPrime(
		BigInteger p
	,	BigInteger s
	,	BigInteger r
	,	BigInteger t
	,	int confidence = 10
	){
		return	(																//true when
					(
							p.isProbablePrime(confidence)						//p - is prime
						&&	s.isProbablePrime(confidence)						//s - is prime
						&&	r.isProbablePrime(confidence)						//r - is prime
						&&	t.isProbablePrime(confidence)						//t - is prime
					)
					&&															//and
					(
						//criteries for a Strong prime:
							( ( (p+1) % s) == 0 )				//(p+1) have divisor s
						&&	( ( (p-1) % r) == 0 )				//(p-1) have divisor r
						&&	( ( (r-1) % t) == 0 )				//(r-1) have divisor t
					)
				)	//		when this all is true - return true, else - false.
		;
	}


	public static Object[] StrongPrime =	new Object[]{
			(BigInteger)new BigInteger()	//	p
		,	(BigInteger)new BigInteger()	//	s
		,	(BigInteger)new BigInteger()	//	r
		,	(BigInteger)new BigInteger()	//	t
		}
	;


	public static Object[] genStrongPrime(	//Gordon's Algorithm, to generate Strong Prime (cryptography).
			int		bits		=	20
		,	int		confidence	=	10
		,	int		maxIter		=	1000
		,	bool	strings		=	false
		,	Random	rand		=	null
	)
	{
		if(object.ReferenceEquals(null, rand)){ rand = new Random(); }
		
		BigInteger s = new BigInteger();
		s.genRandomBits(bits, rand);
		s = s.prevprime();

		BigInteger t = new BigInteger();
		t.genRandomBits(bits, rand);
		t = t.prevprime();
		
		BigInteger r = new BigInteger(4); 					//start - 4, first not prime.
		for(
			BigInteger l = new BigInteger(1);				//from l = 1
			(												//while
					( l <= bitLength(t) )						//l<=t.bitlength()
				&&	!r.isProbablePrime(confidence)				//and r not a prime
			);
			l++												//compute r, and increment l while contition is true
		){
			r = (1 + (l*t));								// r = 1+l*t
		}
		BigInteger p0 = ( ( ( 2 * ( s.modPow( (r-2) , r ) ) ) * s ) - 1 ) ;		//		p0 = ( (2*(s^(r-2) mod r)*s) - 1 )
	
		BigInteger p = new BigInteger(4); 								//start - 4, first not a prime.
		
		int limit = maxIter;											//up to limit iterations in cycle, (1000 by default, if undefined).
		for(
			BigInteger j = new BigInteger(1);							//from start j = 1
			(															//while
					!isStrongPrime(p, s, r, t, 20)						//p is not a strong-prime
				&&	(limit > 0)											//and number of iterations is not reached
			);
			j++															//compute p, and then increment j, and continue
		){
			p = ( p0 + ( ( ( 2 * j ) * r ) * s ) );						//p = p0 + 2*j*r*s
			limit--;													//decrease limit-value
		}

		//	Proof, that prime p, generated with Gordon's algorithm, is a strong-prime:
		//		1. 	s^(r-1) === 1 (mod r) ; -> this is a corollary of Fermat's theorem.
		//			Consequently, p0 = 1 (mod r); p0 = -1 (mod s);
		//		2. After all:
		//			p-1 = p0 + 2jrs - 1 = 0 (mod r);	and (p-1) have divisor r
		//			p+1 = p0 + 2jrs + 1 = 0 (mod s);	and (p+1) have divisor s
		//			r-1 = 2it = 0 (mod t);				and (r-1) have divisor t
		
		
		if(strings == true){
			//Save as strings
			StrongPrime =	new Object[]{
					(string)p.ToString()	//	p
				,	(string)s.ToString()	//	s
				,	(string)r.ToString()	//	r
				,	(string)t.ToString()	//	t
				}
			;
		}else{
			//or save as BigIntegers
			StrongPrime =	new Object[]{
					(BigInteger)p			//	p
				,	(BigInteger)s			//	s
				,	(BigInteger)r			//	r
				,	(BigInteger)t			//	t
				}
			;
		}
		return (
					(isStrongPrime(p, s, r, t))													//if p is a strong prime
						? StrongPrime															//return object with results
					//StrongPrime
						: genStrongPrime(bits, confidence, maxIter, strings, rand)				//else one more try, with default limit.
				)
		;
	}


    /// <summary>
    /// Generates a random number with the specified number of bits such that gcd(number, this) = 1
    /// </summary>
    /// <remarks>
    /// The number of bits must be greater than 0 and less than 2209
    /// </remarks>
    /// <param name="bits">Number of bit</param>
    /// <param name="rand">Random object</param>
    /// <returns>Relatively prime number of this</returns>
    public BigInteger genCoPrime(int bits, Random rand)
    {
        bool done = false;
        BigInteger result = new BigInteger();

        while (!done)
        {
            result.genRandomBits(bits, rand);

            // gcd test
            BigInteger g = result.gcd(this);
            if (g.dataLength == 1 && g.data[0] == 1)
                done = true;
        }

        return result;
    }


    /// <summary>
    /// Generates a random number with the specified number of bits such that gcd(number, this) = 1 (secured)
    /// </summary>
    /// <param name="bits">Number of bit</param>
    /// <param name="rand">Random object</param>
    /// <returns>Relatively prime number of this</returns>
    public BigInteger genCoPrime(int bits, RNGCryptoServiceProvider rand)
    {
        bool done = false;
        BigInteger result = new BigInteger();

        while (!done)
        {
            result.genRandomBits(bits, rand);

            // gcd test
            BigInteger g = result.gcd(this);
            if (g.dataLength == 1 && g.data[0] == 1)
                done = true;
        }

        return result;
    }


    /// <summary>
    /// Returns the modulo inverse of this
    /// </summary>
    /// <remarks>
    /// Throws ArithmeticException if the inverse does not exist.  (i.e. gcd(this, modulus) != 1)
    /// </remarks>
    /// <param name="modulus"></param>
    /// <returns>Modulo inverse of this</returns>
    public BigInteger modInverse(BigInteger modulus)
    {
        BigInteger[] p = { 0, 1 };
        BigInteger[] q = new BigInteger[2];    // quotients
        BigInteger[] r = { 0, 0 };             // remainders

        int step = 0;

        BigInteger a = modulus;
        BigInteger b = this;

        while (b.dataLength > 1 || (b.dataLength == 1 && b.data[0] != 0))
        {
            BigInteger quotient = new BigInteger();
            BigInteger remainder = new BigInteger();

            if (step > 1)
            {
                BigInteger pval = (p[0] - (p[1] * q[0])) % modulus;
                p[0] = p[1];
                p[1] = pval;
            }

            if (b.dataLength == 1)
                singleByteDivide(a, b, quotient, remainder);
            else
                multiByteDivide(a, b, quotient, remainder);

            q[0] = q[1];
            r[0] = r[1];
            q[1] = quotient; r[1] = remainder;

            a = b;
            b = remainder;

            step++;
        }
        if (r[0].dataLength > 1 || (r[0].dataLength == 1 && r[0].data[0] != 1))
            throw (new ArithmeticException("No inverse!"));

        BigInteger result = ((p[0] - (p[1] * q[0])) % modulus);

        if ((result.data[maxLength - 1] & 0x80000000) != 0)
            result += modulus;  // get the least positive modulus

        return result;
    }


    /// <summary>
    /// Returns the value of the BigInteger as a byte array
    /// </summary>
    /// <remarks>
    /// The lowest index contains the MSB
    /// </remarks>
    /// <returns>Byte array containing value of the BigInteger</returns>
    public byte[] getBytes()
    {
        int numBits = bitCount();

        int numBytes = numBits >> 3;
        if ((numBits & 0x7) != 0)
            numBytes++;

        byte[] result = new byte[numBytes];

        int pos = 0;
        uint tempVal, val = data[dataLength - 1];


        if ((tempVal = (val >> 24 & 0xFF)) != 0)
            result[pos++] = (byte)tempVal;

        if ((tempVal = (val >> 16 & 0xFF)) != 0)
            result[pos++] = (byte)tempVal;
        else if (pos > 0)
            pos++;

        if ((tempVal = (val >> 8 & 0xFF)) != 0)
            result[pos++] = (byte)tempVal;
        else if (pos > 0)
            pos++;

        if ((tempVal = (val & 0xFF)) != 0)
            result[pos++] = (byte)tempVal;
        else if (pos > 0)
            pos++;


        for (int i = dataLength - 2; i >= 0; i--, pos += 4)
        {
            val = data[i];
            result[pos + 3] = (byte)(val & 0xFF);
            val >>= 8;
            result[pos + 2] = (byte)(val & 0xFF);
            val >>= 8;
            result[pos + 1] = (byte)(val & 0xFF);
            val >>= 8;
            result[pos] = (byte)(val & 0xFF);
        }

        return result;
    }


    /// <summary>
    /// Sets the value of the specified bit to 1
    /// </summary>
    /// <remarks>
    /// The Least Significant Bit position is 0
    /// </remarks>
    /// <param name="bitNum">The position of bit to be changed</param>
    public void setBit(uint bitNum)
    {
        uint bytePos = bitNum >> 5;             // divide by 32
        byte bitPos = (byte)(bitNum & 0x1F);    // get the lowest 5 bits

        uint mask = (uint)1 << bitPos;
        this.data[bytePos] |= mask;

        if (bytePos >= this.dataLength)
            this.dataLength = (int)bytePos + 1;
    }


    /// <summary>
    /// Sets the value of the specified bit to 0
    /// </summary>
    /// <remarks>
    /// The Least Significant Bit position is 0
    /// </remarks>
    /// <param name="bitNum">The position of bit to be changed</param>
    public void unsetBit(uint bitNum)
    {
        uint bytePos = bitNum >> 5;

        if (bytePos < this.dataLength)
        {
            byte bitPos = (byte)(bitNum & 0x1F);

            uint mask = (uint)1 << bitPos;
            uint mask2 = 0xFFFFFFFF ^ mask;

            this.data[bytePos] &= mask2;

            if (this.dataLength > 1 && this.data[this.dataLength - 1] == 0)
                this.dataLength--;
        }
    }


    /// <summary>
    /// Returns a value that is equivalent to the integer square root of this
    /// </summary>
    /// <remarks>
    /// The integer square root of "this" is defined as the largest integer n, such that (n * n) &lt;= this.
    /// Square root of negative integer is an undefined behaviour (UB).
    /// </remarks>
    /// <returns>Integer square root of this</returns>
    public BigInteger sqrt()
    {
        uint numBits = (uint)this.bitCount();

        if ((numBits & 0x1) != 0)        // odd number of bits
            numBits = (numBits >> 1) + 1;
        else
            numBits = (numBits >> 1);

        uint bytePos = numBits >> 5;
        byte bitPos = (byte)(numBits & 0x1F);

        uint mask;

        BigInteger result = new BigInteger();
        if (bitPos == 0)
            mask = 0x80000000;
        else
        {
            mask = (uint)1 << bitPos;
            bytePos++;
        }
        result.dataLength = (int)bytePos;

        for (int i = (int)bytePos - 1; i >= 0; i--)
        {
            while (mask != 0)
            {
                // guess
                result.data[i] ^= mask;

                // undo the guess if its square is larger than this
                if ((result * result) > this)
                    result.data[i] ^= mask;

                mask >>= 1;
            }
            mask = 0x80000000;
        }
        return result;
    }


    /// <summary>
    /// Returns the k_th number in the Lucas Sequence reduced modulo n
    /// </summary>
    /// <remarks>
    /// Uses index doubling to speed up the process.  For example, to calculate V(k),
    /// we maintain two numbers in the sequence V(n) and V(n+1).
    ///
    /// To obtain V(2n), we use the identity
    ///      V(2n) = (V(n) * V(n)) - (2 * Q^n)
    /// To obtain V(2n+1), we first write it as
    ///      V(2n+1) = V((n+1) + n)
    /// and use the identity
    ///      V(m+n) = V(m) * V(n) - Q * V(m-n)
    /// Hence,
    ///      V((n+1) + n) = V(n+1) * V(n) - Q^n * V((n+1) - n)
    ///                   = V(n+1) * V(n) - Q^n * V(1)
    ///                   = V(n+1) * V(n) - Q^n * P
    ///
    /// We use k in its binary expansion and perform index doubling for each
    /// bit position.  For each bit position that is set, we perform an
    /// index doubling followed by an index addition.  This means that for V(n),
    /// we need to update it to V(2n+1).  For V(n+1), we need to update it to
    /// V((2n+1)+1) = V(2*(n+1))
    ///
    /// This function returns
    /// [0] = U(k)
    /// [1] = V(k)
    /// [2] = Q^n
    ///
    /// Where U(0) = 0 % n, U(1) = 1 % n
    ///       V(0) = 2 % n, V(1) = P % n
    /// </remarks>
    /// <param name="P"></param>
    /// <param name="Q"></param>
    /// <param name="k"></param>
    /// <param name="n"></param>
    /// <returns></returns>
    public static BigInteger[] LucasSequence(BigInteger P, BigInteger Q,
                                             BigInteger k, BigInteger n)
    {
        if (k.dataLength == 1 && k.data[0] == 0)
        {
            BigInteger[] result = new BigInteger[3];

            result[0] = 0; result[1] = 2 % n; result[2] = 1 % n;
            return result;
        }

        // calculate constant = b^(2k) / m
        // for Barrett Reduction
        BigInteger constant = new BigInteger();

        int nLen = n.dataLength << 1;
        constant.data[nLen] = 0x00000001;
        constant.dataLength = nLen + 1;

        constant = constant / n;

        // calculate values of s and t
        int s = 0;

        for (int index = 0; index < k.dataLength; index++)
        {
            uint mask = 0x01;

            for (int i = 0; i < 32; i++)
            {
                if ((k.data[index] & mask) != 0)
                {
                    index = k.dataLength;      // to break the outer loop
                    break;
                }
                mask <<= 1;
                s++;
            }
        }

        BigInteger t = k >> s;

        return LucasSequenceHelper(P, Q, t, n, constant, s);
    }


    //***********************************************************************
    // Performs the calculation of the kth term in the Lucas Sequence.
    // For details of the algorithm, see reference [9].
    //
    // k must be odd.  i.e LSB == 1
    //***********************************************************************
    private static BigInteger[] LucasSequenceHelper(BigInteger P, BigInteger Q,
                                                    BigInteger k, BigInteger n,
                                                    BigInteger constant, int s)
    {
        BigInteger[] result = new BigInteger[3];

        if ((k.data[0] & 0x00000001) == 0)
            throw (new ArgumentException("Argument k must be odd."));

        int numbits = k.bitCount();
        uint mask = (uint)0x1 << ((numbits & 0x1F) - 1);

        // v = v0, v1 = v1, u1 = u1, Q_k = Q^0

        BigInteger v = 2 % n, Q_k = 1 % n,
                   v1 = P % n, u1 = Q_k;
        bool flag = true;

        for (int i = k.dataLength - 1; i >= 0; i--)     // iterate on the binary expansion of k
        {
            while (mask != 0)
            {
                if (i == 0 && mask == 0x00000001)        // last bit
                    break;

                if ((k.data[i] & mask) != 0)             // bit is set
                {
                    // index doubling with addition

                    u1 = (u1 * v1) % n;

                    v = ((v * v1) - (P * Q_k)) % n;
                    v1 = n.BarrettReduction(v1 * v1, n, constant);
                    v1 = (v1 - ((Q_k * Q) << 1)) % n;

                    if (flag)
                        flag = false;
                    else
                        Q_k = n.BarrettReduction(Q_k * Q_k, n, constant);

                    Q_k = (Q_k * Q) % n;
                }
                else
                {
                    // index doubling
                    u1 = ((u1 * v) - Q_k) % n;

                    v1 = ((v * v1) - (P * Q_k)) % n;
                    v = n.BarrettReduction(v * v, n, constant);
                    v = (v - (Q_k << 1)) % n;

                    if (flag)
                    {
                        Q_k = Q % n;
                        flag = false;
                    }
                    else
                        Q_k = n.BarrettReduction(Q_k * Q_k, n, constant);
                }

                mask >>= 1;
            }
            mask = 0x80000000;
        }

        // at this point u1 = u(n+1) and v = v(n)
        // since the last bit always 1, we need to transform u1 to u(2n+1) and v to v(2n+1)

        u1 = ((u1 * v) - Q_k) % n;
        v = ((v * v1) - (P * Q_k)) % n;
        if (flag)
            flag = false;
        else
            Q_k = n.BarrettReduction(Q_k * Q_k, n, constant);

        Q_k = (Q_k * Q) % n;


        for (int i = 0; i < s; i++)
        {
            // index doubling
            u1 = (u1 * v) % n;
            v = ((v * v) - (Q_k << 1)) % n;

            if (flag)
            {
                Q_k = Q % n;
                flag = false;
            }
            else
                Q_k = n.BarrettReduction(Q_k * Q_k, n, constant);
        }

        result[0] = u1;
        result[1] = v;
        result[2] = Q_k;

        return result;
    }


    ////***********************************************************************
    //// Tests the correct implementation of the /, %, * and + operators
    ////***********************************************************************

    //public static void MulDivTest(int rounds)
    //{
    //        Random rand = new Random();
    //    byte[] val = new byte[64];
    //    byte[] val2 = new byte[64];

    //    for(int count = 0; count < rounds; count++)
    //    {
    //            // generate 2 numbers of random length
    //        int t1 = 0;
    //        while(t1 == 0)
    //            t1 = (int)(rand.NextDouble() * 65);

    //        int t2 = 0;
    //        while(t2 == 0)
    //            t2 = (int)(rand.NextDouble() * 65);

    //        bool done = false;
    //        while(!done)
    //        {
    //            for(int i = 0; i < 64; i++)
    //            {
    //                if(i < t1)
    //                    val[i] = (byte)(rand.NextDouble() * 256);
    //                else
    //                    val[i] = 0;

    //                if(val[i] != 0)
    //                    done = true;
    //            }
    //        }

    //        done = false;
    //        while(!done)
    //        {
    //            for(int i = 0; i < 64; i++)
    //            {
    //                if(i < t2)
    //                    val2[i] = (byte)(rand.NextDouble() * 256);
    //                else
    //                    val2[i] = 0;

    //                if(val2[i] != 0)
    //                    done = true;
    //            }
    //        }

    //        while(val[0] == 0)
    //                val[0] = (byte)(rand.NextDouble() * 256);
    //        while(val2[0] == 0)
    //                val2[0] = (byte)(rand.NextDouble() * 256);

    //                Console.WriteLine(count);
    //        BigInteger bn1 = new BigInteger(val, t1);
    //        BigInteger bn2 = new BigInteger(val2, t2);


    //                // Determine the quotient and remainder by dividing
    //                // the first number by the second.

    //        BigInteger bn3 = bn1 / bn2;
    //        BigInteger bn4 = bn1 % bn2;

    //        // Recalculate the number
    //        BigInteger bn5 = (bn3 * bn2) + bn4;

    //                // Make sure they're the same
    //        if(bn5 != bn1)
    //        {
    //            Console.WriteLine("Error at " + count);
    //                        Console.WriteLine(bn1 + "\n");
    //            Console.WriteLine(bn2 + "\n");
    //            Console.WriteLine(bn3 + "\n");
    //                        Console.WriteLine(bn4 + "\n");
    //            Console.WriteLine(bn5 + "\n");
    //            return;
    //        }
    //    }
    //}


    ////***********************************************************************
    //// Tests the correct implementation of the modulo exponential function
    //// using RSA encryption and decryption (using pre-computed encryption and
    //// decryption keys).
    ////***********************************************************************

    //public static void RSATest(int rounds)
    //{
    //        Random rand = new Random(1);
    //    byte[] val = new byte[64];

    //    // private and public key
    //        BigInteger bi_e = new BigInteger("a932b948feed4fb2b692609bd22164fc9edb59fae7880cc1eaff7b3c9626b7e5b241c27a974833b2622ebe09beb451917663d47232488f23a117fc97720f1e7", 16);
    //        BigInteger bi_d = new BigInteger("4adf2f7a89da93248509347d2ae506d683dd3a16357e859a980c4f77a4e2f7a01fae289f13a851df6e9db5adaa60bfd2b162bbbe31f7c8f828261a6839311929d2cef4f864dde65e556ce43c89bbbf9f1ac5511315847ce9cc8dc92470a747b8792d6a83b0092d2e5ebaf852c85cacf34278efa99160f2f8aa7ee7214de07b7", 16);
    //        BigInteger bi_n = new BigInteger("e8e77781f36a7b3188d711c2190b560f205a52391b3479cdb99fa010745cbeba5f2adc08e1de6bf38398a0487c4a73610d94ec36f17f3f46ad75e17bc1adfec99839589f45f95ccc94cb2a5c500b477eb3323d8cfab0c8458c96f0147a45d27e45a4d11d54d77684f65d48f15fafcc1ba208e71e921b9bd9017c16a5231af7f", 16);

    //        Console.WriteLine("e =\n" + bi_e.ToString(10));
    //        Console.WriteLine("\nd =\n" + bi_d.ToString(10));
    //        Console.WriteLine("\nn =\n" + bi_n.ToString(10) + "\n");

    //    for(int count = 0; count < rounds; count++)
    //    {
    //            // generate data of random length
    //        int t1 = 0;
    //        while(t1 == 0)
    //            t1 = (int)(rand.NextDouble() * 65);

    //        bool done = false;
    //        while(!done)
    //        {
    //            for(int i = 0; i < 64; i++)
    //            {
    //                if(i < t1)
    //                    val[i] = (byte)(rand.NextDouble() * 256);
    //                else
    //                    val[i] = 0;

    //                if(val[i] != 0)
    //                    done = true;
    //            }
    //        }

    //        while(val[0] == 0)
    //                val[0] = (byte)(rand.NextDouble() * 256);

    //                Console.Write("Round = " + count);

    //                // encrypt and decrypt data
    //        BigInteger bi_data = new BigInteger(val, t1);
    //                BigInteger bi_encrypted = bi_data.modPow(bi_e, bi_n);
    //                BigInteger bi_decrypted = bi_encrypted.modPow(bi_d, bi_n);

    //                // compare
    //                if(bi_decrypted != bi_data)
    //        {
    //            Console.WriteLine("\nError at round " + count);
    //                        Console.WriteLine(bi_data + "\n");
    //            return;
    //        }
    //        Console.WriteLine(" <PASSED>.");
    //    }

    //}


    ////***********************************************************************
    //// Tests the correct implementation of the modulo exponential and
    //// inverse modulo functions using RSA encryption and decryption.  The two
    //// pseudoprimes p and q are fixed, but the two RSA keys are generated
    //// for each round of testing.
    ////***********************************************************************

    //public static void RSATest2(int rounds)
    //{
    //        Random rand = new Random();
    //    byte[] val = new byte[64];

    //        byte[] pseudoPrime1 = {
    //                (byte)0x85, (byte)0x84, (byte)0x64, (byte)0xFD, (byte)0x70, (byte)0x6A,
    //                (byte)0x9F, (byte)0xF0, (byte)0x94, (byte)0x0C, (byte)0x3E, (byte)0x2C,
    //                (byte)0x74, (byte)0x34, (byte)0x05, (byte)0xC9, (byte)0x55, (byte)0xB3,
    //                (byte)0x85, (byte)0x32, (byte)0x98, (byte)0x71, (byte)0xF9, (byte)0x41,
    //                (byte)0x21, (byte)0x5F, (byte)0x02, (byte)0x9E, (byte)0xEA, (byte)0x56,
    //                (byte)0x8D, (byte)0x8C, (byte)0x44, (byte)0xCC, (byte)0xEE, (byte)0xEE,
    //                (byte)0x3D, (byte)0x2C, (byte)0x9D, (byte)0x2C, (byte)0x12, (byte)0x41,
    //                (byte)0x1E, (byte)0xF1, (byte)0xC5, (byte)0x32, (byte)0xC3, (byte)0xAA,
    //                (byte)0x31, (byte)0x4A, (byte)0x52, (byte)0xD8, (byte)0xE8, (byte)0xAF,
    //                (byte)0x42, (byte)0xF4, (byte)0x72, (byte)0xA1, (byte)0x2A, (byte)0x0D,
    //                (byte)0x97, (byte)0xB1, (byte)0x31, (byte)0xB3,
    //        };

    //        byte[] pseudoPrime2 = {
    //                (byte)0x99, (byte)0x98, (byte)0xCA, (byte)0xB8, (byte)0x5E, (byte)0xD7,
    //                (byte)0xE5, (byte)0xDC, (byte)0x28, (byte)0x5C, (byte)0x6F, (byte)0x0E,
    //                (byte)0x15, (byte)0x09, (byte)0x59, (byte)0x6E, (byte)0x84, (byte)0xF3,
    //                (byte)0x81, (byte)0xCD, (byte)0xDE, (byte)0x42, (byte)0xDC, (byte)0x93,
    //                (byte)0xC2, (byte)0x7A, (byte)0x62, (byte)0xAC, (byte)0x6C, (byte)0xAF,
    //                (byte)0xDE, (byte)0x74, (byte)0xE3, (byte)0xCB, (byte)0x60, (byte)0x20,
    //                (byte)0x38, (byte)0x9C, (byte)0x21, (byte)0xC3, (byte)0xDC, (byte)0xC8,
    //                (byte)0xA2, (byte)0x4D, (byte)0xC6, (byte)0x2A, (byte)0x35, (byte)0x7F,
    //                (byte)0xF3, (byte)0xA9, (byte)0xE8, (byte)0x1D, (byte)0x7B, (byte)0x2C,
    //                (byte)0x78, (byte)0xFA, (byte)0xB8, (byte)0x02, (byte)0x55, (byte)0x80,
    //                (byte)0x9B, (byte)0xC2, (byte)0xA5, (byte)0xCB,
    //        };


    //        BigInteger bi_p = new BigInteger(pseudoPrime1);
    //        BigInteger bi_q = new BigInteger(pseudoPrime2);
    //        BigInteger bi_pq = (bi_p-1)*(bi_q-1);
    //        BigInteger bi_n = bi_p * bi_q;

    //    for(int count = 0; count < rounds; count++)
    //    {
    //            // generate private and public key
    //                BigInteger bi_e = bi_pq.genCoPrime(512, rand);
    //                BigInteger bi_d = bi_e.modInverse(bi_pq);

    //                Console.WriteLine("\ne =\n" + bi_e.ToString(10));
    //                Console.WriteLine("\nd =\n" + bi_d.ToString(10));
    //                Console.WriteLine("\nn =\n" + bi_n.ToString(10) + "\n");

    //            // generate data of random length
    //        int t1 = 0;
    //        while(t1 == 0)
    //            t1 = (int)(rand.NextDouble() * 65);

    //        bool done = false;
    //        while(!done)
    //        {
    //            for(int i = 0; i < 64; i++)
    //            {
    //                if(i < t1)
    //                    val[i] = (byte)(rand.NextDouble() * 256);
    //                else
    //                    val[i] = 0;

    //                if(val[i] != 0)
    //                    done = true;
    //            }
    //        }

    //        while(val[0] == 0)
    //                val[0] = (byte)(rand.NextDouble() * 256);

    //                Console.Write("Round = " + count);

    //                // encrypt and decrypt data
    //        BigInteger bi_data = new BigInteger(val, t1);
    //                BigInteger bi_encrypted = bi_data.modPow(bi_e, bi_n);
    //                BigInteger bi_decrypted = bi_encrypted.modPow(bi_d, bi_n);

    //                // compare
    //                if(bi_decrypted != bi_data)
    //        {
    //            Console.WriteLine("\nError at round " + count);
    //                        Console.WriteLine(bi_data + "\n");
    //            return;
    //        }
    //        Console.WriteLine(" <PASSED>.");
    //    }

    //}


    ////***********************************************************************
    //// Tests the correct implementation of sqrt() method.
    ////***********************************************************************

    //public static void SqrtTest(int rounds)
    //{
    //        Random rand = new Random();
    //    for(int count = 0; count < rounds; count++)
    //    {
    //            // generate data of random length
    //        int t1 = 0;
    //        while(t1 == 0)
    //            t1 = (int)(rand.NextDouble() * 1024);

    //                Console.Write("Round = " + count);

    //                BigInteger a = new BigInteger();
    //                a.genRandomBits(t1, rand);

    //                BigInteger b = a.sqrt();
    //                BigInteger c = (b+1)*(b+1);

    //                // check that b is the largest integer such that b*b <= a
    //                if(c <= a)
    //        {
    //            Console.WriteLine("\nError at round " + count);
    //                        Console.WriteLine(a + "\n");
    //            return;
    //        }
    //        Console.WriteLine(" <PASSED>.");
    //    }
    //}



    //public static void Main(string[] args)
    //{
    //        // Known problem -> these two pseudoprimes passes my implementation of
    //        // primality test but failed in JDK's isProbablePrime test.

    //        byte[] pseudoPrime1 = { (byte)0x00,
    //                (byte)0x85, (byte)0x84, (byte)0x64, (byte)0xFD, (byte)0x70, (byte)0x6A,
    //                (byte)0x9F, (byte)0xF0, (byte)0x94, (byte)0x0C, (byte)0x3E, (byte)0x2C,
    //                (byte)0x74, (byte)0x34, (byte)0x05, (byte)0xC9, (byte)0x55, (byte)0xB3,
    //                (byte)0x85, (byte)0x32, (byte)0x98, (byte)0x71, (byte)0xF9, (byte)0x41,
    //                (byte)0x21, (byte)0x5F, (byte)0x02, (byte)0x9E, (byte)0xEA, (byte)0x56,
    //                (byte)0x8D, (byte)0x8C, (byte)0x44, (byte)0xCC, (byte)0xEE, (byte)0xEE,
    //                (byte)0x3D, (byte)0x2C, (byte)0x9D, (byte)0x2C, (byte)0x12, (byte)0x41,
    //                (byte)0x1E, (byte)0xF1, (byte)0xC5, (byte)0x32, (byte)0xC3, (byte)0xAA,
    //                (byte)0x31, (byte)0x4A, (byte)0x52, (byte)0xD8, (byte)0xE8, (byte)0xAF,
    //                (byte)0x42, (byte)0xF4, (byte)0x72, (byte)0xA1, (byte)0x2A, (byte)0x0D,
    //                (byte)0x97, (byte)0xB1, (byte)0x31, (byte)0xB3,
    //        };

    //        byte[] pseudoPrime2 = { (byte)0x00,
    //                (byte)0x99, (byte)0x98, (byte)0xCA, (byte)0xB8, (byte)0x5E, (byte)0xD7,
    //                (byte)0xE5, (byte)0xDC, (byte)0x28, (byte)0x5C, (byte)0x6F, (byte)0x0E,
    //                (byte)0x15, (byte)0x09, (byte)0x59, (byte)0x6E, (byte)0x84, (byte)0xF3,
    //                (byte)0x81, (byte)0xCD, (byte)0xDE, (byte)0x42, (byte)0xDC, (byte)0x93,
    //                (byte)0xC2, (byte)0x7A, (byte)0x62, (byte)0xAC, (byte)0x6C, (byte)0xAF,
    //                (byte)0xDE, (byte)0x74, (byte)0xE3, (byte)0xCB, (byte)0x60, (byte)0x20,
    //                (byte)0x38, (byte)0x9C, (byte)0x21, (byte)0xC3, (byte)0xDC, (byte)0xC8,
    //                (byte)0xA2, (byte)0x4D, (byte)0xC6, (byte)0x2A, (byte)0x35, (byte)0x7F,
    //                (byte)0xF3, (byte)0xA9, (byte)0xE8, (byte)0x1D, (byte)0x7B, (byte)0x2C,
    //                (byte)0x78, (byte)0xFA, (byte)0xB8, (byte)0x02, (byte)0x55, (byte)0x80,
    //                (byte)0x9B, (byte)0xC2, (byte)0xA5, (byte)0xCB,
    //        };

    //        Console.WriteLine("List of primes < 2000\n---------------------");
    //        int limit = 100, count = 0;
    //        for(int i = 0; i < 2000; i++)
    //        {
    //                if(i >= limit)
    //                {
    //                        Console.WriteLine();
    //                        limit += 100;
    //                }

    //                BigInteger p = new BigInteger(-i);

    //                if(p.isProbablePrime())
    //                {
    //                        Console.Write(i + ", ");
    //                        count++;
    //                }
    //        }
    //        Console.WriteLine("\nCount = " + count);


    //        BigInteger bi1 = new BigInteger(pseudoPrime1);
    //        Console.WriteLine("\n\nPrimality testing for\n" + bi1.ToString() + "\n");
    //        Console.WriteLine("SolovayStrassenTest(5) = " + bi1.SolovayStrassenTest(5));
    //        Console.WriteLine("RabinMillerTest(5) = " + bi1.RabinMillerTest(5));
    //        Console.WriteLine("FermatLittleTest(5) = " + bi1.FermatLittleTest(5));
    //        Console.WriteLine("isProbablePrime() = " + bi1.isProbablePrime());

    //        Console.Write("\nGenerating 512-bits random pseudoprime. . .");
    //        Random rand = new Random();
    //        BigInteger prime = BigInteger.genPseudoPrime(512, 5, rand);
    //        Console.WriteLine("\n" + prime);

    //        //int dwStart = System.Environment.TickCount;
    //        //BigInteger.MulDivTest(100000);
    //        //BigInteger.RSATest(10);
    //        //BigInteger.RSATest2(10);
    //        //Console.WriteLine(System.Environment.TickCount - dwStart);

    //}
	
	
//--------------------BEGIN RSABigInteger:--------------------

//	//Description the following code up to the end.
//	RSA allow to do the following RSA-operations:
//		1. Encrypt (by publicKey) the message to cipher, and decrypt that message (by privateKey) from cipher.
//			e - public exponent, n - modulus, d - secret exponent, (e, n) - publicKey, (d, n) - privateKey,
//			m - message, c - encrypted message (cipher), m_ - decrypted message.
//				1.	Alice:		Generate privateKey (d, n), and get publicKey (e, n), from this privateKey.
//				2.	Alice:		Send she's publicKey (e, n) to another correspondent, to Bob.
//				3.	Bob:		c = m^e mod n;			- 		Encrypt data by publicKey.
//				4.	Bob:		c 						->		Send this computed cipher to Alice.
//				5.	Alice:		m_ = c^d mod n			-		Decrypt data into m_ by she's secure priveteKey.
//				Property:		m_ == m					-		decrypted message, this is equal of original Bob's open-message.
//
//		2. Sign (by privateKey) the message to signature, and extract that message (by publicKey) from signature.
//			e - public exponent, n - modulus, d - secret exponent, (e, n) - publicKey, (d, n) - privateKey,
//			m - message, s - sinature, m_ - extracted message.
//				1.	Alice:	s = m ^ d mod n				-	generate digital signature "s" ( encrypt message "m" by privKey "(d, n)" )
//				2.	Alice:	(m, s)						->	send to another correspondent, Bob.
//				3.	Bob:	m_ = s ^ e mod n			-	extract message from "s" ( decrypt cipher "s", by pubKey "(e, n)" )
//				4.	Bob:	(m_ == m)					-	Verify signature (compare existing "m" with decrypted "m_")
//
//	All this operations can be processed, using fast modPow function, when:
//		n is a some BigInteger;
//		m, e, d - BigIntegers, with value up to (n-1);
//		then, c and s can have value up to (n-1) too (just because power is by modulus n).
//
//	Lengths of values:
//		1.
//			All values of "c" (c = m^e mod n), just because this is by modulus n, this values are contains in range [0, ..., (n-1)].
//			(n-1) is a maximum, because next value, n, will be encrypted as: (n mod n) = 0 = (0 mod n).
//			So (n-1) is max value in that range, including of this, with including the null too.
//		
//		2.	Property of RSA encrypt-decrypt actions: m can be unequivocally encrypted to c, and unequivocally decrypted back from c, by modulus n.
//		
//		3.	When m = n, ( c = (m^e mod n) = (n^e mod n) = 0 = (0^e mod n) ).
//			In this case you can see the repetition of the output value "c",
//			and this can not be decrypted unequivocally, to "n" (decrypted message = 0).
//		
//		4.	Thus, means m can be in range [0, ... (n-1)] too, and m^e can give an unique values,
//			which by modulus n, can give unique values in the same range: [0, ... (n-1)].
//		
//		5.	So, "m"-value, as decimal value (BigInteger), can not be greater than (n-1),
//			and this value must to contains, in range [0, ..., (n-1)].
//		
//		6. 	In this case, bitlength of "m"-value can contains in range [0, ..., (n_bitlength-1)],
//			where (n_bitlength-1) - max bitlength of decimal "m"-value (BigInteger).
//			
//		7.	Max bytelength of c-value, "c_bytelength" is ( ( ( n_bitlength - ( n_bitlength % 8 ) ) / 8 ) + ((( n_bitlength % 8 ) > 0)?1:0) )
//			so bytelength of "m"-value, must contains in range [ 0, ..., ( c_bytelength - 1 ) ].
//		
//		7.	Then any "m", with this (bit/byte)-lengths, will be a number, with value in range [0, ..., (n-1)],
//			and this can be unequivocally encrypted to "c", and decrypted back, from "c".
//			
//		8.	Property:
//			m
//			with bitlength in range [0, ..., (n_bitlength-1)]
//			or with bytelength in range [ 0, ..., ( c_bytelength - 1 ) ],
//			encrypting into c
//			with bitlength in range [0, ..., n_bitlength]
//			or with bitlength in range [0, ..., c_bytelength].
//	
//	All this allow to do encryption/decryption the data with arbitrary length,
//	by read and write this as blocks with specified (bit/byte)-lengths.
//	Because of different blocklengths, the following operations are not a reversive-operations:
//
//	Encryption data, with arbitrary byte length:
//		1.	Read source data of "m", with arbitrary length, block-by-block,
//				with block-bitlength (n_bitlength-1),
//				or with block-bytelength ( c_bytelength - 1 ),
//				into blocks m0, m1, m2, m3, m4, ... m;
//		2.	Convert each block to BigIntegers, with value in range [0, ... (n-1)];
//		3.	Encrypt by PubKey, the each BigInteger into "c" in range [0, ... (n-1)],
//				with max bitlength n_bitlength,
//				or max bytelength c_bytelength.
//		4.	Convert BigIntegers to bytes, and write this in correct offsets, in the blocks with fixed lengths.
//		5.	Write blocks with encrypted cypher in output cypher blocks-by-blocks.
//		6.	Add ulong-value (8 bytes), with the length of last block, in the end of encrypted data.
//
//	Decryption cipher, into data with arbitrary byte length:
//		1.	Read ulong value with the length of last block, in the end of file (last 8 bytes).
//		2.	Read cipher "c", with arbitrary length, block-by-block,
//				with block-bitlength (n_bitlength),
//				or with block-bytelength c_bytelength,
//				and read up to the end, into blocks c0, c1, c2, c3, c4, ..., c;
//		2.	Convert each block to BigInteger, with value in range [0, ..., (n-1)].
//		3.	Decrypt by PrivKey, the each BigInteger into "m_" in range [0, ..., (n-1)],
//				with max bitlength (n_bitlength-1),
//				or max bytelength ( c_bytelength - 1 ).
//		4.	Convert BigIntegers to bytes, and write this in correct offsets, in the blocks.
//		5.	Write blocks with decrypted data blocks-by-blocks.
//		6.	Skip ulong-value with last block bytelength, in the end, in readed data with cypher.
//
//	This two methods allow to encrypt-decrypt files, and bytearrays, and binary data, with arbitrary length.
//		byte[] encryptedBytes = BigInteger.EncryptBytes(PrivOrPubKeyFileOrXMLStringKey, byte[] sourceBytes, UseBigInteger, ByPriv);
//		byte[] decryptedBytes = BigInteger.DecryptBytes(PrivOrPubKeyFileOrXMLStringKey, byte[] sourceBytes, UseBigInteger, ByPub);
//	
//	Extended methods for RSACryptoServiceProvider, in the "public static class RsaExtensions":
//		byte[] encryptByPriv = (BigInteger.rsa).EncryptByPrivateKey(sourceBytes);	//return bytes
//		byte[] decryptByPub = (BigInteger.rsa).DecryptByPublicKey(encryptByPriv);	//return bytes

//		Implement this all, using BigIntegers,
//		because
//		RSACryptoServiceProvider.Encrypt() return another cypher, which is incompatible with decrypt as BigIntegers, and can encrypt only with pubKey, but not PrivKey.
//		RSACryptoServiceProvider.Decrypt() can decrypt only with PrivKey, but not PubKey.
//		The following code will implement encrypt/decrypt the data with arbitrary length, EncryptBytes(pub/priv) and DecryptBytes(priv/pub), using BigIntegers.
//		optionally, there is possible to Encrypt

	
	public static bool enableLog = true;
	
	public static void log(string str){
		if(enableLog==true){
			File.AppendAllText("debug.log", str+"\n");	//add string to debug.log
		}
	}

	//	extended methods
	public static	string		Bi2Base64	( BigInteger bi )								//BigInteger -> to Base64-string.
	{
		return ( System.Convert.ToBase64String( bi	.getBytes() ) );
	}

	public static	BigInteger	B64ToBi		( string b64	)								//Base64-string -> to BigInteger.
	{
		return new BigInteger(Convert.FromBase64String(b64));
	}
	
	//	Methods to work with Files and with ByteArrays.
	public static	byte[]		Combine		(byte[] first, byte[] second)					//Combine, and concatenate two bytearrays.
	{
		byte[] bytes = new byte[first.Length + second.Length];
		Buffer.BlockCopy(first, 0, bytes, 0, first.Length);
		Buffer.BlockCopy(second, 0, bytes, first.Length, second.Length);
		return bytes;
	}

	public static	bool		CompareFiles(string first_path="", string second_path="", bool UpToEnd = false)	//Compare two files (filepaths).
	{
		System.IO.FileInfo first = new System.IO.FileInfo( first_path );
		System.IO.FileInfo second = new System.IO.FileInfo( second_path );
				
		if (first.Length != second.Length){
			log("Files lengths of files not equal! first.Length: "+first.Length+" != second.Length: "+second.Length);
			return false;
		}
		if (string.Equals(first.FullName, second.FullName, StringComparison.OrdinalIgnoreCase)){
			log("Same file, fullNames are equal! first.FullName: "+first.FullName+", second.FullName: "+second.FullName);
			return true;
		}

		//else, if length is equal, and this is not the same file... Compare files by each byte:
		using (FileStream fs1 = first.OpenRead()){
			using (FileStream fs2 = second.OpenRead())
			{
				bool NotEqual = false;
				for (int i = 0; i < first.Length; i++)			//for each byte, up to first.length
				{
					int first_ith_byte = fs1.ReadByte();		//read byte from first file to int
					int second_ith_byte = fs2.ReadByte();		//read byte from second file to int
					if ( first_ith_byte != second_ith_byte){	//if not equal
						log(
							"Byte i: "+i+
							" not equal! "+first_ith_byte+		
							"(1) !== "+second_ith_byte+"(2)"
						);
						if(UpToEnd==true){
							NotEqual = true;
						}else{
							return false;							//and return false
						}
					}
				}
				if(NotEqual == true){return false;}
			}
		}
		return true;											//else, if all bytea are equal - return true.
	}

	public static	bool		CompareBytes(byte[] one, byte[] two) 						//Compare two bytearrays with SequenceEqual ("using System.Linq;")
	{ 
		return one.SequenceEqual(two);
	}
	
	public static	void		WriteAnotherFileIfExists(string filename, string data){		//Try to save "data" in "filename", or add timestamp to "filename", if "filename" already exists.
		if (System.IO.File.Exists(filename)){
			log("File with filename "+filename+" is already exists!");
			filename = DateTime.Now.ToFileTime()+filename;
			log("Generate new filename: "+filename);
		}
		System.IO.StreamWriter writter = System.IO.File.CreateText(filename);
		writter.Write(data);
		writter.Close();
		return;
	}
	

	//	public static fields to save RSA-keys.
	//	rsa, pa_Priv, pa_Pub - if RSA-key.
	//	e_value, d_value, n_value (and another - if UseBigInteger==true)

	//when BigInteger not used for generated keys...
	public static RSACryptoServiceProvider	rsa					=	new RSACryptoServiceProvider();					//define new RSACryptoServiceProvider
	public static RSAParameters				pa_Priv				=	new RSAParameters();							//define new RSAParameters pa_Priv.
	public static RSAParameters				pa_Pub				=	new RSAParameters();							//define new RSAParameters pa_Pub.
	
	// When BigInteger used for generated keys...
	public static BigInteger				e_value				=	new BigInteger();								//define new BigInteger e_value.
	public static BigInteger				d_value				=	new BigInteger();								//define new BigInteger d_value.
	public static BigInteger				n_value				=	new BigInteger();								//define new BigInteger n_value.

	//another values to save from keyFiles.
	public static BigInteger				p_value				=	new BigInteger();								//define new BigInteger p_value.
	public static BigInteger				q_value				=	new BigInteger();								//define new BigInteger q_value.
	public static BigInteger				dp_value			=	new BigInteger();								//define new BigInteger dp_value.
	public static BigInteger				dq_value			=	new BigInteger();								//define new BigInteger dq_value.
	public static BigInteger				InverseQ_value		=	new BigInteger();								//define new BigInteger InverseQ_value.

	public static string					xml_privKey			=	""					;							//privKey.
	public static string					xml_pubKey			=	""					;							//pubKey.
	
	
	public static void SaveXMLKeys(
		bool UseBigInteger = false
	)
	{
			if(UseBigInteger == false){									//if BigInteger not used to generate RSA-keys

				if(!rsa.PublicOnly){
					xml_privKey = rsa.									//from rsa
												ToXmlString(true)			//export privkey
												.Replace("<", "\n\t<")		//and format this as multistring
												.Replace(">",">\n\t\t")
												.Replace("\t\t\n","")
												.Replace("\t</RSAKeyValue>\n\t\t","</RSAKeyValue>")
												.Replace("\n\t<R","<R")
					;
				}
				xml_pubKey = rsa.									//from rsa
											ToXmlString(false)			//export pubkey
												.Replace("<", "\n\t<")	//and format this as multistring
												.Replace(">",">\n\t\t")
												.Replace("\t\t\n","")
												.Replace("\t</RSAKeyValue>\n\t\t","</RSAKeyValue>")
												.Replace("\n\t<R","<R")
				;
			}
			else{														//if BigInteger was used to generate RSA-keys
				if(		!	(	d_value.Equals(		new BigInteger()	)	)	)	{
					xml_privKey =	""									//generate XML-string for privkey
											+	"<RSAKeyValueBigInteger>"
											+		"<Modulus>"		+	( Bi2Base64(n_value			) )	+	"</Modulus>"
											+		"<Exponent>"	+	( Bi2Base64(e_value			) )	+	"</Exponent>"
											+		"<P>"			+	( Bi2Base64(p_value			) )	+	"</P>"
											+		"<Q>"			+	( Bi2Base64(q_value			) )	+	"</Q>"
											+		"<DP>"			+	( Bi2Base64(dp_value		) )	+	"</DP>"
											+		"<DQ>"			+	( Bi2Base64(dq_value		) )	+	"</DQ>"
											+		"<InverseQ>"	+	( Bi2Base64(InverseQ_value	) )	+	"</InverseQ>"
											+		"<D>"			+	( Bi2Base64(d_value			) )	+	"</D>"
											+	"</RSAKeyValueBigInteger>"	//and replace <RSAKeyValue> to <RSAKeyValueBigInteger>.
											//This means <Exponent> was been generated as co-prime number and not last five Fermat's prime-number. 
					;
				
					xml_privKey = 	xml_privKey					//format this string, as multiString, and replce
										.Replace("<", "\n\t<")
										.Replace(">",">\n\t\t")
										.Replace("\t\t\n","")
										.Replace("\t</RSAKeyValueBigInteger>\n\t\t","</RSAKeyValueBigInteger>")
										.Replace("\n\t<R","<R")
					;
				}
				else{
					xml_privKey = "";
				}
				
				xml_pubKey =	""									//generate XML-string for puKey
										+	"<RSAKeyValueBigInteger>"
										+		"<Modulus>"		+	( Bi2Base64(n_value			) )	+	"</Modulus>"
										+		"<Exponent>"	+	( Bi2Base64(e_value			) )	+	"</Exponent>"
										+	"</RSAKeyValueBigInteger>"	//and replace <RSAKeyValue> to <RSAKeyValueBigInteger>.
										//This means <Exponent> was been generated as co-prime number and not last five Fermat's prime-number. 
				;
				
				xml_pubKey = 	xml_pubKey						//format this string, as multiString, and replce
									.Replace("<", "\n\t<")
									.Replace(">",">\n\t\t")
									.Replace("\t\t\n","")
									.Replace("\t</RSAKeyValueBigInteger>\n\t\t","</RSAKeyValueBigInteger>")
									.Replace("\n\t<R","<R")
				;
			}
	}

	public static void GenerateRSAKeys(	//Save generated RSA-keys in rsa, pa_Priv, and pa_pub - if RSA-keys and UseBigInteger==false, or in BigIntegers, if UseBigInteger == true.
		bool UseBigInteger = false			//use BigInteger methods, to generate this keys, or use RSACryptoServiceProvider(bitlength)? (true/false)
	,	int bitlength = 512					//bitlength can be specified, default value = 512, just for test (this is faster)
	)
	{
//		log("GenerateRSAKeys - bitlength: "+bitlength);
		//start generate RSA-keys
		if(UseBigInteger == false){									//if no need to use BigInteger
			try{														//try
//				log("GenerateRSAKeys - UseBigInteger === false");
				rsa = new RSACryptoServiceProvider(bitlength);				//Generate new RSA key with specified bitlength, or default
				//and save this into rsa, pa_Priv, pa_Pub.
				pa_Priv	=	rsa.ExportParameters(true);						//export parameters of privkey
				pa_Pub	=	rsa.ExportParameters(false);					//export parameters of pubkey
			}catch (Exception ex){										//if exception
				log( "Error:" + ex.ToString());							//show this
			}
		}
		else if (UseBigInteger == true){							//if need to use BigInteger	
			try{
				Random rand = new Random();												//new random generator

//				BigInteger bi_p = BigInteger.genPseudoPrime(bitlength/2, 40, rand);		//p
//				BigInteger bi_q = BigInteger.genPseudoPrime(bitlength/2, 40, rand);		//q


				//	Use Safe-Primes for p and q:
				BigInteger bi_p = BigInteger.genSafePrime((bitlength/2),10,"previous",0,rand);		//p
				BigInteger bi_q = bi_p;																	//q is p, on start.
				while(bi_q.Equals(bi_p)){																//while q == p
					bi_q		=	BigInteger.genSafePrime((bitlength/2),10,"previous",0,rand);		//generate safe prime q != p, with half-bitlength of n.
				}

		//		//	Use Strong-Primes for p and q:
		//		BigInteger bi_p = (BigInteger)BigInteger.genStrongPrime((bitlength/2))[0];							//p
		//		BigInteger bi_q = bi_p;																				//q is p, on start.
		//		while(bi_q.Equals(bi_p)){																			//while q == p
		//			bi_q		=	(BigInteger)BigInteger.genStrongPrime((bitlength/2))[0];						//generate safe prime q != p, with half-bitlength of n.
		//		}


				BigInteger bi_n = bi_p * bi_q;												//n = p*q

				BigInteger lambdaN 		=	(bi_p - 1).lcm((bi_q - 1));						//lambdaN
				BigInteger bi_e 		=	lambdaN.genCoPrime(bitlength/2, rand);
				BigInteger bi_d			=	bi_e.modInverse(lambdaN);						//lambdaN - d			=	( e^(−1) mod phi_n ) - is working, because (phi_n % λ(n) === 0), and for when (d*e ≡ 1 (mod λ(n))), (d*e ≡ 1 (mod λ(n))) too. But (d > λ(n)) can be true.
				
			//	if( bi_e <= bi_d ){										//if e lesser or equals d
			//		BigInteger temp = bi_d; bi_d = bi_e; bi_e = temp;	//swap bi_e <-> bi_d
			//	}														//to return e, lesser than d, to keep secret a longer d.

				BigInteger bi_dp		=	bi_d % (bi_p - 1);									//dp		=	(	d mod (p−1)		)
				BigInteger bi_dq		=	bi_d % (bi_q - 1);									//dq		=	(	d mod (q−1)		)
				BigInteger bi_InverseQ	=	bi_q.modInverse(bi_p);								//inverseQ	=	(	q^(−1) mod p	)

				//Try to save this generated valued into rsa, pa_Priv, pa_Pub, or into BigIntegers.
				//
				//	XML RSA-keys format: 
				//	<RSAKeyValue>
				//		<Modulus>	Base64-encoded-number	</Modulus>
				//		<Exponent>	Base64-encoded-number	</Exponent>
				//		<P>			Base64-encoded-number	</P>
				//		<Q>			Base64-encoded-number	</Q>
				//		<DP>		Base64-encoded-number	</DP>
				//		<DQ>		Base64-encoded-number	</DQ>
				//		<InverseQ>	Base64-encoded-number	</InverseQ>
				//		<D>			Base64-encoded-number	</D>
				//	</RSAKeyValue>
				//
				//	n	-	Modulus
				//	e	-	Exponent
				//	p	-	P
				//	q	-	Q
				//	d	-	D
				//
				//	dp	-	DP, this is ( d mod (p−1) ), 
				//	dq	-	DQ, this is ( d mod (q−1) ),
				//	InverseQ - this is ( q^(−1) mod p ).
				//
				//	These are used in applying the Chinese Remainder Theorem to RSA decryption, which is an optimization technique.
				//

				try{
					//Generate xml-string with RSA-privKey
					string xmlString =	""
										+	"<RSAKeyValue>"
										+		"<Modulus>"		+	( Bi2Base64(	bi_n		) )	+	"</Modulus>"
										+		"<Exponent>"	+	( Bi2Base64(	bi_e		) )	+	"</Exponent>"
										+		"<P>"			+	( Bi2Base64(	bi_p		) )	+	"</P>"
										+		"<Q>"			+	( Bi2Base64(	bi_q		) )	+	"</Q>"
										+		"<DP>"			+	( Bi2Base64(	bi_dp		) )	+	"</DP>"
										+		"<DQ>"			+	( Bi2Base64(	bi_dq		) )	+	"</DQ>"
										+		"<InverseQ>"	+	( Bi2Base64(	bi_InverseQ	) )	+	"</InverseQ>"
										+		"<D>"			+	( Bi2Base64(	bi_d		) )	+	"</D>"
										+	"</RSAKeyValue>"
					;
					//Format this as a multistring.
					xmlString = 	xmlString
									.Replace("<", "\n\t<")
									.Replace(">",">\n\t\t")
									.Replace("\t\t\n","")
									.Replace("\t</RSAKeyValue>\n\t\t","</RSAKeyValue>")
									.Replace("\n\t<R","<R")
					;
					//import PrivKey to rsa from xml-string
					rsa.FromXmlString(xmlString);						//here throw exception, when e is co-prime, and not last Fermat's prime.
					pa_Priv	=	rsa.ExportParameters(true);				//export parameters of privkey
					pa_Pub	=	rsa.ExportParameters(false);			//export parameters of pubkey
				}
				catch //(Exception ex)		//on error
				{
				//	log( "Error on saving Keys as rsa, pa_Priv, pa_Pub:" + ex);	//show this

				//	log( "Save keys as BigInteger-values...");
					try{																		//and try to save generated key-values, as BigIntegers.
						//save pub (e,n) and priv (d, n);
						e_value = bi_e;
						d_value = bi_d;
						n_value = bi_n;
					
						//save another values.
						p_value				=	bi_p;
						q_value				=	bi_q;
						dp_value			=	bi_dp;
						dq_value			=	bi_dq;
						InverseQ_value		=	bi_InverseQ;
					
						//reset this values
						rsa					=	new RSACryptoServiceProvider();					//define new RSACryptoServiceProvider
						pa_Priv				=	new RSAParameters();							//define new RSAParameters pa_Priv.
						pa_Pub				=	new RSAParameters();							//define new RSAParameters pa_Pub.
				//		log( "Done.");
					}
					catch	(Exception ex){												//on error
						log( "Error:" + ex.ToString());								//show this
					}
				}
			}
			catch	(Exception ex)																//if some error
			{
				log( "Error:" + ex.ToString());												//show this
			}
		}
		
//		log("GenerateRSAKeys. SaveXMLKeys(UseBigInteger), UseBigInteger: "+UseBigInteger);
		SaveXMLKeys(UseBigInteger);
	}
	
	public static void GenerateRSAKeysAndSave(	//Generate RSA-keys and save this as XML-keys, into the files
		string privKeyFile						//File to save PrivKey
	,	string pubKeyFile						//File to save PubKey
	,	bool UseBigInteger = false				//use BigInteger methods, to generate this keys, or use RSACryptoServiceProvider(bitlength)? (true/false)
	,	int bitlength = 512						//bitlength can be specified, default value = 512, just for test (this is faster)
	)
	{
		try
		{
			//Generate RSA-keys, and save this in (rsa, pa_Priv, pa_Pub)-values, or into BigIntegers.
			GenerateRSAKeys(
				UseBigInteger,				//use BigInteger methods, to generate this keys, or not? (true/false)
				bitlength					//bitlength, default value = 512, just for test (this is faster)
			);

			//Save keys in files.
			WriteAnotherFileIfExists(privKeyFile, xml_privKey);		//write PrivKey in file
			WriteAnotherFileIfExists(pubKeyFile, xml_pubKey);		//Write PubKey in file
		}
		catch (Exception ex)			//on error
		{
			log("ex: "+ex.ToString());		//show this.
		}
	}
	
	public static void LoadKeyFile(			//Load keys (priv+pub) or pub only if pubKey
		string KeyFile 						//from KeyFile or string with XML-pubKey or XML-privKey.
	,	bool UseBigInteger = false			//load this as RSA-key into (rsa, pa_Priv, pa_Pub)-values, or load into BigInteger-values (true/false)
	)
	{
		string xmlString = (												//get XML-string of privKey or pubKey
								(KeyFile.Contains("<Modulus>"))					//if KeyFile, this is a string with key
									? KeyFile										//use this string as xmlString
									: System.IO.File.ReadAllText(KeyFile)			//or open file and read XML-key from file with xml.
		);
		UseBigInteger = (xmlString.Contains("RSAKeyValueBigInteger")) ? true : UseBigInteger;

		if(
				!xmlString.Contains("RSAKeyValueBigInteger")				//if BigInteger not been used to generate this key in xmlString
			&&	UseBigInteger == false										//and if no need to UseBigInteger, to load key into BigIntegers
		){																		//Load this key into (rsa, pa_Priv, and pa_Pub)-values.
		
																				//extract public key from "key"-file with xmlString.
			rsa.FromXmlString(xmlString);										//and load key there, in RSACryptoServiceProvider rsa.
		
			if(xmlString.Contains("<D>")){										//if this was been a privkey, and this contains <D>-value of privKey (d, n)
				pa_Priv =	rsa.ExportParameters(true);								//export privateKey from this to pa_Priv
			}
			pa_Pub	=	rsa.ExportParameters(false);								// (or/and) export the publicKey from this to pa_Pub.
			
			//then, leave empty values for all those BigInteger:
			n_value			=	new BigInteger();
			e_value			=	new BigInteger();
			p_value			=	new BigInteger();
			q_value			=	new BigInteger();
			dp_value		=	new BigInteger();
			dq_value		=	new BigInteger();
			InverseQ_value	=	new BigInteger();
			d_value			=	new BigInteger();
		}
		else if (												//else if
				xmlString.Contains("RSAKeyValueBigInteger")		//BigInteger not been used to generate this key in xmlString
			||	UseBigInteger == true							//or if need to load this key into BigInteger-values
																//(for example, to do encrypt-by-priv, and decrypt-by-pub, using extended methods)
		)
		{
			//Then, load this key, into BigInteger-values:
			
			//Load values from xml-string
			var LoadedKey = XElement.Parse(xmlString);				//need to "using System.Xml";

			if(xmlString.Contains("<D>")){												//if this was been a privKey, and this contains <D>-value
				//decode values from base64 fields of XML - and import this into BigIntegers
				n_value			=	B64ToBi((string)LoadedKey.Element("Modulus"));			//	n
				e_value			=	B64ToBi((string)LoadedKey.Element("Exponent"));			//	e
				p_value			=	B64ToBi((string)LoadedKey.Element("P"));				//	p
				q_value			=	B64ToBi((string)LoadedKey.Element("Q"));				//	q
				dp_value		=	B64ToBi((string)LoadedKey.Element("DP"));				//	dp
				dq_value		=	B64ToBi((string)LoadedKey.Element("DQ"));				//	dq
				InverseQ_value	=	B64ToBi((string)LoadedKey.Element("InverseQ"));			//	InverseQ
				d_value			=	B64ToBi((string)LoadedKey.Element("D"));				//	d
			}
			else{																		//else if this was been pubKey
				e_value			=	B64ToBi((string)LoadedKey.Element("Exponent"));			//	e
				n_value			=	B64ToBi((string)LoadedKey.Element("Modulus"));			//	n - (e, n)-only is a pubKey.
				p_value			=	new BigInteger();										//	and leave
				q_value			=	new BigInteger();										//	this values
				dp_value		=	new BigInteger();										//	all
				dq_value		=	new BigInteger();										//	as
				InverseQ_value	=	new BigInteger();										//	an empty
				d_value			=	new BigInteger();										//	values
			}
		}
//		log("LoadKeyFile. KeyFile"+KeyFile+", SaveXMLKeys(UseBigInteger), UseBigInteger: "+UseBigInteger);
		SaveXMLKeys(UseBigInteger);
		//After all, key from keyFile, or from xmlString, is loaded into (rsa, pa_Priv, pa_Pub)-values, or into BigIntegers.
	}

	
//
//	EncryptFile, will encrypt file [src], into file [dest],
//	EncryptBytes, will encrypt bytearray [src], into bytearray [dest],
//	both will encrypt [src] to [dest]
//	by using pubkey from file [key],
//	or by using pubkey, which was been extracted from privkey in file [key],
//	or by using privKey from file [key], when byPriv == true (sign the message, and generate the digital signature).
//	
//	(d, n) - privkey, (e, n) - pubkey; e - public exponent, d - private exponent, n - modulus, c - ciphertext, 
//	c	= m ^ (e or d) mod n;		- encryption by pubkey or privkey (sign),
//	m'	= c ^ (d or e) mod n;		- decryption by privkey or pubkey (extract message from signature to verify it),
//	
//	cypherBytelength = ( ( ( n_bitlength - ( n_bitlength % 8 ) ) / 8 ) + ((( n_bitlength % 8 ) > 0)?1:0) );
//	File will be splitted by blocks with ( cypherBytelength - 1 ) bytes.
//	This blocks will be encrypted by pubkey from "key", or pubkey which is extracted from prikey "key".
//	Pubkey - is (e, n), where n, this is a modulus - a big number with specified n_bitlength.
//	The result ciphertext have n_bitlength bits, or cypherBytelength bytes, and will be writted by blocks in encrypted file.
//
//	Last block will be encrypted as is, but after encrypted block will be added ulong-value (8 bytes) with LastBlockLength.
//

	public static int SubtractBytes, block_size, block_length;	//define this variables.
	
	public static int bitLength(BigInteger value){
//		log("bitLength - value:"+value.ToString());
		int bitLength = 0;
		do
		{
			bitLength++;
			value /= 2;
		} while(value != 0);
//		log("bitLength - bitLength:"+bitLength);
//		log("bitLength - value.byteLength:"+value.getBytes().Length);
		return bitLength;
	}
	
	private static void set_lengths(	//set lengths of blocks to read-write
		int n_bitlength					//bitlength of modulus n from KeyFile
	,	bool UseBigInteger = false		//Use BigInteger to encrypt-decrypt-data or not? true/false
	)
	{
//			log("set_lengths - n_bitlength: "+n_bitlength);
			//
			//	For rsa.Encrypt() and rsa.Decrypt():
			//		Having looked at some of the information on RSA encryption modes,
			//		it would appear that PKCS#1 v1.5 (which is calling as rsa.Encrypt(..., false), and rsa.Decrypt(..., false))
			//		"...can operate on messages of length up to k - 11 octets (k is the octet length of the RSA modulus)"
			//	
			//	For BigInteger.EncryptFile(), BigInteger.EncryptBytes(), BigInteger.DecryptFile(), BigInteger.DecryptBytes():
			//		dest_maxBitLength = n_bitlength;
			//		dest_maxBitLength = ( ( ( n_bitlength - ( n_bitlength % 8 ) ) / 8 ) + ((( n_bitlength % 8 ) > 0)?1:0) );
			//		where "dest_maxBitLength" - n_bitlength of modulus n-value in key.
			//		
			//		src_maxBitlength = dest_maxBitLength - 1;
			//		src_maxByteLength = dest_maxBitLength - 1;
			//
			
			//set this values:
			SubtractBytes = ((UseBigInteger == true ) ? 1 : 11);											//select how many bytes need to subtract from each block.

			block_size           =         (															//block length for destination file = n_bytelength (+ 1, when n_bitlength%8 > 0).
													( 
														(
															n_bitlength
															-
															( n_bitlength % 8 )
														)
														/
														8
													)
													+
													(
														(
															( n_bitlength % 8 ) > 0
														)
														? 1
														: 0
													)
												);
			block_length         =         block_size-SubtractBytes;									//block length for source file
			
			return;	//and return, then.
	}


	private static BigInteger CRTAcceleration(BigInteger value){
//		log("Start CRTAcceleration");
		//		By definition of this method of accelleration, propose the following thing:
		//			2 modPow with exp 512 bits, by modulus 512 bits + 1 adding + 1 mulmod,
		//			all this is faster then 1 modPow with exponent 1024 bits, and faster in 2-3 times, for many values.
		//		This accelleration working only for encrypt by privKey (signing the data), or decrypt by privKey (decrypt encrypted data), not by a pubKey.
	
		//		Description:
		//		//	additional key values:
		//		d_P = d mod (p-1);
		//		d_Q = d mod (q-1);
		//		InverseQ = q^(-1) mod (p) = q.modInv(p);
		//		____________________________________________________________________________________________
		//		//	where this is defined:
		//		d_P			-	RSA_key.dp
		//		d_Q			-	RSA_key.dq
		//		InverseQ	-	RSA_key.InverseQ
		//			This values, defined, after load key.
		//		____________________________________________________________________________________________
		//		Steps:
		//		//faster decrypt (by priv), or sign-encrypt (when sign message by priv):
		//		m_p = C^(d_P) mod p
		//		m_q = C^(d_Q) mod q
		//		h = (InverseQ * (m_p + ( ( m_p < m_q ) ? [q/p]*p : 0 ) - m_q)) mod p
		//		m = (m_q + hq) mod (p*q) = (m_q + hq) mod n;
		//			where, C - ciphertext (encrypted by pubKey, and which is try to decrypt by privKey), or message (which is try to be signed by privKey);
		//			d_P, d_Q, InverseQ - additional key values; p, q - prime numbers as components of privKey; m - decrypted message, or signature. 

		BigInteger m_p = value.modPow(dp_value, p_value);				//		m_p = C^(d_P) mod p
		BigInteger m_q = value.modPow(dq_value, q_value);				//		m_q = C^(d_Q) mod q
		//		h = (InverseQ * (m_p + ( ( m_p < m_q ) ? [q/p]*p : 0 ) - m_q)) mod p
		BigInteger h = ( ( InverseQ_value * ( m_p + ( ( m_p < m_q ) ? ( ( ( ( q_value - ( q_value % p_value ) ) / p_value ) + 1 ) * p_value ) : 0 ) - m_q ) ) % p_value );
		BigInteger result = ( ( m_q + ( h * q_value ) ) % n_value ) ;		//		m = (m_q + hq) mod (p*q);

//		//Test 1:
//			log("( dp == d % (p - 1) ) ? "+(dp_value == d_value % (p_value - 1)));
//			log("( dq == d % (q - 1) ) ? "+(dq_value == d_value % (q_value - 1)));
//			log("( InverseQ ==  q.modInverse(p) ) ? "+(InverseQ_value == q_value.modInverse(p_value)));
//		//Test 2:
//			log("test is CRTequal (result == value ^ d % n ) ? "+(result == value.modPow(d_value, n_value)));

		return result;		//return BigInteger, with value from 0 up to (n-1);
	}

//
//	Encrypt file [src], into file [dest], by using pubkey from file [key],
//	or by using pubkey, which was been extracted from privkey in file [key].
//	(d, n) - privkey, (e, n) - pubkey;
//	c	= m ^ e mod n;		- encryption by public key
//	m'	= c ^ d mod n;		- decryption by private key.
//
//	File will be splitted by blocks with ((bitlength/8) - 1) bytes.
//	This blocks will be encrypted by pubkey from "key", or pubkey which is extracted from prikey "key".
//	Pubkey - is (e, n), where n, this is a modulus - a big number with specified n_bitlength.
//	The result ciphertext have n_bitlength bits, and will be writted by blocks in encrypted file.
//
//	Last block will be encrypted as is, but after encrypted block will be added ulong-value (8 bytes) with LastBlockLength.
//

	//
	//	Encryption file or bytearray:
	//		1. Read file by blocks (KeyLength-SubtractBytes)
	//		2. Encrypt each block by pub or priv, and write this in the block with KeyLength.
	//		3. Block-by-block, up to the end of file.
	//		4. Add ulong value (8 bytes) with length of last block, in the end of encrypted data.
	//		6. Write this all in file, or in bytearray.
	//		
	//		Three methods used to encrypt data:
	//		public static	void	EncryptFullBlockOrLastBlock	-	encrypt one block, and write this in ref.
	//		public static	byte[]	EncryptFullBlockOrLastBlock	-	return bytearray.
	//		public static	void	EncryptFile					-	encrypt, and write as file
	//		private static	void	EncryptBytes				-	encrypt and write bytearray by ref
	//		public static	byte[]	EncryptBytes				-	encrypt, and return bytearray.
	//

	
	//
	//	Encrypt one block from "buffer", with "block_size", in each iteration of read "data",
	//	or encrypt last block in "buffer" with length "c",
	//	and save the encrypted ciphertext in "encbuffer", by reference (ref).
	//	Encrypt this by pubkey, which is contains in "rsa",
	//	and encrypt with rsa.Encrypt(), or BigInteger modPow method - UseBigInteger (true/false);
	//	
	//	This method will be called on each iteratio of reading blocks of "source data",
	//	as from an FileStream, or MemoryStream.
	//	
	//	Encrypted data will contains in "encbuffer".
	//
	
	
	public static	void	EncryptFullBlockOrLastBlock(	//encrypt full block or last block inside the cycles.
		ref RSACryptoServiceProvider rsa	//RSACryptoServiceProvider, with imported pubKey
	,	ref byte[] buffer					//readed buffer from the source file
	,	ref byte[] encbuffer				//already defined encbuffer, as reference
	,	ref int block_size					//already defined block_size, as reference
	,	ref int c							//number of readed bytes, as reference
	,	ref bool UseBigInteger				//use BigInteger or not? true/false
	,	ref BigInteger ed					//(if UseBigInteger = true, then) ed - e or d. e (public exponent), if encrypt by pubkey (e, n); or d (secret exponent), if encrypt by privkey (d, n)
	,	ref BigInteger n					//(if UseBigInteger = true, then) n - modulus
	,	bool CRT=false						//use CRTAccelleration, or not? true(for priv only)/false
	)
	{
//		log("ed: "+ed.ToString());
//		log("n: "+n.ToString());
		encbuffer = new byte[block_size];	//create new encbuffer with block_size.
		if (c == buffer.Length)				//if this was been readed a full block, and not a last block - just encrypt it.
		{
			if(UseBigInteger == false){									//if no need to use BigInteger modPow to encrypt
				encbuffer = rsa.Encrypt(buffer, false);						//just encrypt by using rsa.Encrypt()
			}else{														//else
//				log("(new BigInteger	(buffer))"+(new BigInteger	(buffer)));
			
//			log("EncryptFullBlockOrLastBlock in: "+(new BigInteger	(buffer)).ToString());

				//use BigInteger
				BigInteger		bi_encryptedBuffer = (									//and encrypt there
							( CRT == true && ( dp_value != 0 && dq_value != 0 && InverseQ_value != 0 ) )
							? CRTAcceleration((new BigInteger	(buffer)))
							:(
								(new BigInteger	(buffer))						//the buffer
								.modPow	(										//by using modPow method
									ed,											//to encrypt this buffer, into BigInteger, by e or d
									n											//and modulus n
								)
							)
						)
				;
//			log("EncryptFullBlockOrLastBlock out: "+(new BigInteger	(bi_encryptedBuffer)).ToString());
				
				byte[] encryptedBuffer = bi_encryptedBuffer.getBytes();										//define new bytearray for encryptedBuffer (this can have a different bytelength)
				
//				log("(new BigInteger	(encryptedBuffer))"+(new BigInteger	(encryptedBuffer)));
				//independent of bytelength of result bytearray, write this in the encbuffer
				Buffer.BlockCopy(encryptedBuffer, 0, encbuffer, (encbuffer.Length-encryptedBuffer.Length), encryptedBuffer.Length);
			}
		}
		else //else if last block, and readed bytes not equals of buffer length.
		{
			//slice this buffer up to c-value:
			byte[] buffer2 = new byte[c];
			for (int i = 0; i < c; i++){
				buffer2[i] = buffer[i];
			}

			if(UseBigInteger == false){						//if no need to use BigInteger to encrypt
				encbuffer = rsa.Encrypt(buffer2, false);		//just use rsa.Encrypt()
			}else{											//else
//				log("(new BigInteger	(buffer2))"+(new BigInteger	(buffer2)));
				//use BigInteger
				byte[] encryptedBuffer;						//define new encrypted buffer for result, this can have different length
					encryptedBuffer = (							//and encrypt
						( CRT == true && ( dp_value != 0 && dq_value != 0 && InverseQ_value != 0 ) )
						? CRTAcceleration((new BigInteger	(buffer2)))
						:(
							(new BigInteger	(buffer2))				//buffer2
								.modPow	(ed, n)						//by using BigInteger modPow method
						)
					)
					.getBytes()								//and get bytes from result BigInteger, then.
				;
//				log("(new BigInteger	(encryptedBuffer))"+(new BigInteger	(encryptedBuffer)));
				
				//after this, write bytes of result BigInteger with cypher, into encbuffer, independent of bytelength of this result.
				Buffer.BlockCopy(encryptedBuffer, 0, encbuffer, (encbuffer.Length-encryptedBuffer.Length), encryptedBuffer.Length);
			}

			//After encryption of last block of the source data, add ulong with the length of this block, in the end of encrypted result.
			if(UseBigInteger == true){									//only if BigInteger modPow used for encryption
				ulong number = Convert.ToUInt64(c);						//the number of readed data bytes
				byte[] LastBlockLength = new byte[8];					//create bytearray with 8 bytes
				LastBlockLength = BitConverter.GetBytes(number);		//convert ulong to bytearray
				if (BitConverter.IsLittleEndian){						//if this bytes was been LittleEndian
					Array.Reverse(LastBlockLength);						//Reverse the bytearray
				}

				encbuffer = Combine(encbuffer, LastBlockLength);			//and append this 8 bytes with ulong value in the end of encrypted data
			}
		}
		//after this all, encbuffer by that reference, will contains an encrypted ciphertext, and this can be writted.
	}

	public static	byte[]	EncryptFullBlockOrLastBlock(	//The same, but this method will return encbuffer, as bytearray.
		ref RSACryptoServiceProvider rsa	//RSACryptoServiceProvider, where pubKey is already imported.
	,	ref byte[] buffer					//readed buffer
	,	ref int block_size					//block_size of this
	,	ref int c							//length of readed buffer
	,	ref bool UseBigInteger				//encrypt with BigInteger modPow method - true, or with rsa.Encrypt() - false;
	,	ref BigInteger ed
	,	ref BigInteger n
	,	bool CRT = false
	)
	{
		byte[] encbuffer = new byte[block_size];	//define encbuffer, as a bytearray

		EncryptFullBlockOrLastBlock(				//encrypt
			ref rsa,
			ref buffer,
			ref encbuffer,							//and save result in encbuffer by reference
			ref block_size,
			ref c,
			ref UseBigInteger,
			ref ed,
			ref n,
			CRT
		);

		return encbuffer;					//return encbuffer.
	}

	public static	void	EncryptFile(	//Encrypt src-file to dest-file by pubKey or privKey
		string key = ""						//key for encrypt - the file/xml-string pub, or with xml-priv, to get pub from it, if byPriv == false, else with priv.
	,	string src = ""						//src - input file to encrypt
	,	string dest = ""					//dest - output file save encryted ciphertext
	,	bool UseBigInteger = false			//true - use, false - use rsa.Encrypt() and rsa.Decrypt()
	,	bool byPriv = false					//default encryption, by publicKey - false, else - true, and encrypt by priv, to decrypt by pub (sign the message, to verify result cipher as signature).
	)
	{
		LoadKeyFile(key, UseBigInteger);	//extract public key from "key"-file with xml.

		int n_bitlength = 0;

		if(UseBigInteger == false){
			n_bitlength = rsa.KeySize;													//then, get n_bitlength of modulus from RSA-key.
		}
		else{
			//n_bitlength = n_value.dataLength * 32;
			n_bitlength = bitLength(n_value);
		}

		//create two FileStreams
		System.IO.FileStream fin = System.IO.File.Open(src, System.IO.FileMode.Open, System.IO.FileAccess.Read, System.IO.FileShare.Read);			//FileStream for input file
		System.IO.FileStream fout = System.IO.File.Open(dest, System.IO.FileMode.Create, System.IO.FileAccess.Write, System.IO.FileShare.Write);	//FileStream for output file

		//and try to encrypt the source file "src", with this pubkey.
		try
		{
			set_lengths(n_bitlength, UseBigInteger);

			System.IO.FileInfo finfo = new System.IO.FileInfo( src );					//get file info of src-file

			byte[] buffer = new byte[ block_length ];									//set size of block to read the source file
			byte[] encbuffer = new byte[ block_size ];									//set size of block to write in destination encrypted file
			int c = 0;																	//srart value of count = 0

			BigInteger ed = null;
			BigInteger n = null;

			if(UseBigInteger == false){													//if no need to use BigInteger
				ed = (
					(byPriv == true)														//if byPriv == true
					?	new BigInteger	(pa_Priv.D)												//then, d -> to BigInteger
					:	new BigInteger	(pa_Pub.Exponent)										//else, e -> to BigInteger
				);
				n = (new BigInteger	(pa_Pub.Modulus));										//n -> to BigInteger
			}else{																		//else, if UseBigInteger: 
				ed = (
					(byPriv == true)														//if byPriv == true
					?	d_value																	//then, d -> to BigInteger
					:	e_value																	//else, e -> to BigInteger
				);
				n = n_value;																//n -> to BigInteger
			}
			while ((c = fin.Read(buffer, 0, block_length )) > 0)	//for each block of readed source file, including the last block
			{
				//encrypt by pub into the encbuffer, using rsa.Encrypt() or BigInteger.
				encbuffer = EncryptFullBlockOrLastBlock(ref rsa, ref buffer, ref block_size, ref c, ref UseBigInteger, ref ed, ref n, byPriv);
				fout.Write(encbuffer, 0, encbuffer.Length);			//and write encbuffer into the destination file.
				buffer = new byte[ block_length ];
			}
			fin.Close();	//after all, close input file
			fout.Close();	//and close output file
		}
		catch (Exception ex)	//if try fails, show throw exception
		{
			fin.Close();
			fout.Close();
			log( "\nError:" + ex.ToString());
		}
	}

	
	//	Encrypt bytearray from src to dest, by using pubkey in key, and encrypt it with BigInteger modPow, or with rsa.Encrypt();
	
	private static	void	EncryptBytes(	//The same but encrypt bytearrays, anc create MemoryStreams, instead of FileStreams
		string key							//key - pub, for encrypt, or priv, to get pub from it, and encrypt then, if byPriv == false. This can be xml-string with key too.
	,	ref byte[] src						//reference to bytearray with source data	
	,	ref byte[] dest						//reference to bytearray with destination cipher data
	,	bool UseBigInteger = false			//Need use BigInteger, or use rsa.Encrypt()? true/false
	,	bool byPriv = false					//encrypt by privKey to sing the message, and decrypt by pubKey, then.
	)
	{
		LoadKeyFile(key, UseBigInteger);			//extract public key from "key"-file with xml.
		int n_bitlength = 0;
		
		if(UseBigInteger == false){
			n_bitlength = rsa.KeySize;													//then, get n_bitlength of RSA-key.
		}
		else{
			//n_bitlength = n_value.dataLength * 32;
			n_bitlength = bitLength(n_value);
		}

		MemoryStream fin 	=	new MemoryStream(src);	//Create new MemoryStream for src
		MemoryStream fout	=	new MemoryStream();		//Create new MemoryStream for dest

		try
		{
			set_lengths(n_bitlength, UseBigInteger);
			
			byte[] buffer = new byte[ block_length ];
			byte[] encbuffer = new byte[ block_size ];
			int c = 0;

			BigInteger ed = null;
			BigInteger n = null;
			
			if(UseBigInteger == false){													//if no need to use BigInteger
				ed = (
					(byPriv == true)														//if byPriv == true
					?	new BigInteger	(pa_Priv.D)												//then, d -> to BigInteger
					:	new BigInteger	(pa_Pub.Exponent)										//else, e -> to BigInteger
				);
				n = (new BigInteger	(pa_Pub.Modulus));										//n -> to BigInteger
			}else{																		//else, if UseBigInteger: 
				ed = (
					(byPriv == true)														//if byPriv == true
					?	d_value																	//then, d -> to BigInteger
					:	e_value																	//else, e -> to BigInteger
				);
				n = n_value;																//n -> to BigInteger
			}

			while ((c = fin.Read(buffer, 0, block_length )) > 0)
			{
//				log("enc: buffer: "+BitConverter.ToString(buffer).Replace("-", string.Empty)+" "+buffer.Length);
				//encrypt by pub or priv into the encbuffer, using rsa.Encrypt() or BigInteger.
				encbuffer = EncryptFullBlockOrLastBlock(ref rsa, ref buffer, ref block_size, ref c, ref UseBigInteger, ref ed, ref n, byPriv);
				fout.Write(encbuffer, 0, encbuffer.Length);			//and write encbuffer into the destination file.
//				log("enc: encbuffer: "+BitConverter.ToString(encbuffer).Replace("-", string.Empty)+" "+encbuffer.Length);
				buffer = new byte[ block_length ];
			}
			fin.Close();
			dest = fout.ToArray();
			fout.Close();
		}
		catch (Exception ex)
		{
			fin.Close();
			dest = fout.ToArray();
			fout.Close();
			log( "\nError:" + ex.ToString());
		}
	}
		
	
	//	return "dest"-bytearray
	
	public static	byte[]	EncryptBytes(	//The same, but return "dest"-bytearray with encrypted-cipher
		string key
	,	byte[] src
	,	bool UseBigInteger = false
	,	bool byPriv = false
	)
	{
		byte[] dest = new byte[0];
		EncryptBytes(
			key
		,	ref src
		,	ref dest
		,	UseBigInteger
		,	byPriv
		);
		return dest;
	}



	//
	//	Decryption file or bytearray:
	//		1. Read file by blocks with KeyLength
	//		2. Decrypt each block by pub or priv, and write this in the block with (KeyLength-SubtractBytes).
	//		3. Block-by-block, up to the end of file.
	//		4. skip ulong value (8 bytes) with length of last block, in the end of encrypted data.
	//		6. Write this all in file, or in bytearray.
	//		
	//		Three methods used to encrypt data:
	//		public static	void	DecryptFullBlockOrLastBlock	-	decrypt one block, and write this in ref.
	//		public static	byte[]	DecryptFullBlockOrLastBlock	-	return bytearray.
	//		public static	void	DecryptFile					-	decrypt file, and write as file.
	//		private static	void	DecryptBytes				-	decrypt bytearray, and write bytearray by ref
	//		public static	byte[]	DecryptBytes				-	decrypt and return bytearray
	//


	
	//
	//	Decrypt one block from "buffer", with "block_size", in each iteration of read "cipherdata",
	//	or encrypt last block in "buffer" with length "c",
	//	and save the encrypted ciphertext in "encbuffer", by reference (ref).
	//	Encrypt this by pubkey, which is contains in "rsa",
	//	and encrypt with rsa.Encrypt(), or BigInteger modPow method - UseBigInteger (true/false);
	//	
	//	This method will be called on each iteration of reading blocks of "source data",
	//	as from an FileStream, or MemoryStream.
	//	
	//	Encrypted data will contains in "encbuffer".
	//

	public static	void	DecryptFullBlockOrLastBlock(	//Decrypt full block or last block inside the cycle.
		ref RSACryptoServiceProvider rsa	//RSACryptoServiceProvider, with imported pubKey
	,	ref byte[] buffer					//readed buffer from the source file
	,	ref byte[] decbuffer				//already defined decbuffer, as reference
	,	ref int block_size					//already defined block_size, as reference
	,	ref int c							//number of readed bytes, as reference
	,	ref bool isNextUlong				//is next value ulong or not? true/false
	,	bool UseBigInteger 	= 	false		//use BigInteger or not? true/false
	,	int dataLength 		= 	0			//Length of data
	,	BigInteger de 		= 	null		//de - d or e. d (secret exponent) - if decrypt by priv (d, n), (by default); or e (pubic exponent) - if decrypt by pub (verify signature)
	,	BigInteger n 		= 	null		//n - modulus
	,	int current_block 	= 	0			//number of the current block
	,	int max_blocks 		= 	0			//number of the max block to decrypt
	,	ulong length__ 		= 	0			//length of last block
	,	bool CRT			=	false
	)
	{
		if(UseBigInteger == true){
			//rewrite buffer, when this is a last block, and have no block_length size.
			if (c != block_size)
			{
				byte[] buffer2 = new byte[c];
				for (int i = 0; i < c; i++){
					buffer2[i] = buffer[i];
				}
				buffer = buffer2;
			}
										
			int rest = (int)( dataLength - ( current_block * block_size ) );
			if		( rest <= 0 ){
				//here is full ulong, in this block

				//slice buffer on 8 bytes, and cut ulong-value
				byte[] NewBuffer = new byte[buffer.Length-8];
				Buffer.BlockCopy(buffer, 0, NewBuffer, 0, NewBuffer.Length);
				buffer = NewBuffer;
			}
			else if	( rest < 8 ){
				//here is the partial of ulong, in this block, and partial in the next block.

				int PartOfLenHere = 8 - rest;	//number of bytes in this block

				//slice buffer on PartOfLenHere bytes, and cut ulong-value
				byte[] NewBuffer = new byte[buffer.Length-PartOfLenHere];
					Buffer.BlockCopy(buffer, 0, NewBuffer, 0, NewBuffer.Length);
					buffer = NewBuffer;
					isNextUlong = true;
			}
			else if	( rest == 8 ){
				return;
			}
		}

		if(UseBigInteger == false){
			decbuffer = rsa.Decrypt(buffer, false);
		}
		else{
			int BufferLength = ( ( current_block == max_blocks-1 ) ? (int)length__ : ( block_size - SubtractBytes ) );		//length__ !
			
			byte[] decryptedBuffer = new byte[ BufferLength ];
			decbuffer = new byte[ BufferLength ];
			
//			log("DecryptFullBlockOrLastBlock de: "+de.ToString()+"n: "+n.ToString());
//			log("DecryptFullBlockOrLastBlock in: "+(new BigInteger	(buffer)).ToString());
			
			BigInteger bi_decryptedBuffer = 	(
									( CRT == true && ( dp_value != 0 && dq_value != 0 && InverseQ_value != 0 ) )
									? CRTAcceleration((new BigInteger	(buffer)))
									: (
										(new BigInteger	(buffer))
										.modPow(de, n)
									)
								)
								
			;

//			log("DecryptFullBlockOrLastBlock out: "+bi_decryptedBuffer.ToString());
			
			decryptedBuffer = bi_decryptedBuffer.getBytes();
			
			Buffer.BlockCopy(decryptedBuffer, 0, decbuffer, (decbuffer.Length-decryptedBuffer.Length), decryptedBuffer.Length);
		}
		//after this all, decrypted value will contains in decbuffer by reference.
	}

	
	//	This method will return encbuffer, as bytearray.
	
	public static	byte[]	DecryptFullBlockOrLastBlock(	//decrypt full block or last block inside the cycle.
		ref RSACryptoServiceProvider rsa	//RSACryptoServiceProvider, with imported pubKey
	,	ref byte[] buffer					//readed buffer from the source file
	,	ref int block_size					//already defined block_size, as reference
	,	ref int c							//number of readed bytes, as reference
	,	ref bool isNextUlong				//is next value ulong or not? true/false
	,	bool UseBigInteger	=	false		//use BigInteger or not? true/false
	,	int dataLength		=	0			//Length of data
	,	BigInteger de		=	null		//de - d or e. d (secret exponent) - if decrypt by priv (d, n), (by default); or e (pubic exponent) - if decrypt by pub (verify signature)
	,	BigInteger n		=	null		//n - modulus
	,	int current_block	=	0			//number of the current block
	,	int max_blocks		=	0			//number of the max block to decrypt
	,	ulong length__		=	0			//length of last block
	,	bool CRT			=	false
	)
	{
		byte[] decbuffer = new byte[0];		//define encbuffer, as a bytearray

		//encrypt full block or last block inside the cycle.
		DecryptFullBlockOrLastBlock(
			ref rsa								//RSACryptoServiceProvider, with imported pubKey
		,	ref buffer							//readed buffer from the source file
		,	ref decbuffer						//already defined decbuffer, as reference
		,	ref block_size						//already defined block_size, as reference
		,	ref c								//number of readed bytes, as reference
		,	ref isNextUlong						//is next value ulong or not? true/false
		,	UseBigInteger						//use BigInteger or not? true/false
		,	dataLength							//Length of data
		,	de									//de - d or e. d (secret exponent) - if decrypt by priv (d, n), (by default); or e (pubic exponent) - if decrypt by pub (verify signature)
		,	n									//n - modulus
		,	current_block						//number of the current block
		,	max_blocks							//number of the max block to decrypt
		,	length__							//length of last block
		,	CRT
		);
		return decbuffer;						//return decbuffer.
	}
		

	//
	//	Decrypt encrypted file, by priv.
	//	(d, n) - privkey, where n have n_bitlength size, and n_bytelength.
	//	encrypted file readed by blocks with n_bytelength,
	//	this block will be decrypted, then result will writted to blocks with bytelength (n_bytelenght - 1).
	//	Last 8 bytes of encrypted file, this is ulong value with bytelength of last block.
	//	This value will be readed at beginning, and then this value need to skip, and slice the bytes of last block, then.
	//
	public static	void	DecryptFile(
		string key				=	""			//privKey to decrypt by default, or pubKey of owners, to verify the signature, by encrypting the message by owner's privKey
	,	string src				=	""
	,	string dest				=	""
	,	bool UseBigInteger		=	false
	,	bool byPub				=	false
	)
	{
		ulong length__ = 0;													//define this ulong as 0
		
		if(UseBigInteger == true)											//if BigInteger modPow used for decryption, then this was been encrypted with modPow.
		{
			//read 8 bytes with last block length from the end of file.
			byte[] LastBlockLength = new byte[8];							//8 bytes
			using (BinaryReader reader = new BinaryReader(new FileStream(src , FileMode.Open)))	//open file
			{
				reader.BaseStream.Seek( ( ( new System.IO.FileInfo( src ) ).Length - 8 ), SeekOrigin.Begin);	//and read from the end
				reader.Read(LastBlockLength, 0, 8);																//8 bytes
				reader.Close();																					//then close file
				reader.Dispose();
			}
			BigInteger LastBlockLength_Bi = (new BigInteger	(LastBlockLength));									//convert LastBlockLength to BigInteger
			length__ = Convert.ToUInt64(LastBlockLength_Bi.ToString());											//then convert this to ulong.
		}
		//else, ulong value with last block length, is not contains in the end of file, in last 8 bytes.
		
		//open src and dest files as FileStreams
		System.IO.FileStream fin = System.IO.File.Open	(	src,	System.IO.FileMode.Open, System.IO.FileAccess.Read, System.IO.FileShare.Read);			//src
		System.IO.FileStream fout = System.IO.File.Open	(	dest,	System.IO.FileMode.Create, System.IO.FileAccess.Write, System.IO.FileShare.Write);		//dest
		
		//and try to decrypt src
		try
		{

			LoadKeyFile(key, UseBigInteger);			//extract public key from "key"-file with xml.
			int n_bitlength = 0;
			if(UseBigInteger == false){
				n_bitlength = rsa.KeySize;													//then, get n_bitlength of modulus from RSA-key.
			}
			else{
				//n_bitlength = n_value.dataLength * 32;
				n_bitlength = bitLength(n_value);
			}

			set_lengths(n_bitlength, UseBigInteger);

			System.IO.FileInfo finfo = new System.IO.FileInfo(src);		//create FileInfo for encrypted-file, to get length of this.
			int dataLength = (int)finfo.Length;								//get length of file.
			
			byte[] buffer = new byte[block_size];						//define buffer with length of block for reading encrypted file
			byte[] decbuffer = new byte[block_length];		//define decbuffer with length of block for write decrypted file
			
			BigInteger de, n;
			if(UseBigInteger == false)
			{
				de = (
					(byPub == true)
						?	new BigInteger	(pa_Pub.Exponent)
						:	new BigInteger	(pa_Priv.D)
				);				//extract secret exponent, and convert to BigInteger.
				n = (
					new BigInteger	(
						(
							(byPub == true)
								? pa_Pub
								: pa_Priv
						).Modulus
					)
				);			//extract modulus and confert to BigInteger.
			}
			else{
				de	=	( (byPub == true) ? e_value : d_value);
				n	=	n_value;
			}
			
			int max_blocks = (int)(finfo.Length / block_size);
			int current_block = 0;
			
			int c = 0;
			
			bool	isNextUlong = false;
			
			while ((c = fin.Read(buffer, 0, block_size)) > 0)  //читать файл блоками по block_size
			{
				if(UseBigInteger == true && isNextUlong == true){
					break;
				}
			
				decbuffer = DecryptFullBlockOrLastBlock(
					ref rsa
				,	ref buffer
				,	ref block_size
				,	ref c
				,	ref isNextUlong
				,	UseBigInteger
				,	dataLength
				,	de
				,	n
				,	current_block
				,	max_blocks
				,	length__
				,	!byPub
				);
				
				fout.Write(decbuffer, 0, decbuffer.Length); //write this later.
				current_block += 1;
			}
			fin.Close();
			fout.Close();
		}
		catch (ArgumentException ex)// when (e.ParamName == "…")
		{
			fin.Close();
			fout.Close();
			log("ex.ParamName: "+ex.ParamName);
		}
		catch (Exception ex)
		{
			fin.Close();
			fout.Close();
			log("ex: "+ex.ToString());
		}
	}

	//
	//	Decrypt encrypted bytearray with cipher, by priv.
	//	(d, n) - privkey, where n have n_bitlength size, and n_bytelength.
	//	encrypted file readed by blocks with n_bytelength,
	//	this block will be decrypted, then result will writted to blocks with bytelength (n_bytelenght - 1).
	//	Last 8 bytes of encrypted file, this is ulong value with bytelength of last block.
	//	This value will be readed at beginning, and then this value need to skip, and slice the bytes of last block, then.
	//
	private static	void	DecryptBytes(
		string key						//file with priv or pub
	,	ref byte[] src					//reference on src-bytes
	,	ref byte[] dest					//reference on dest-bytes
	,	bool UseBigInteger = false		//UseBigInteger or not? true/false
	,	bool byPub = false
	)
	{
		ulong length__ = 0;
		if(UseBigInteger == true)
		{
			//read 8 bytes with last block length from the end of file.
			byte[] LastBlockLength = new byte[8];

			Buffer.BlockCopy(src, src.Length-8, LastBlockLength, 0, 8);

			BigInteger LastBlockLength_Bi = (new BigInteger	(LastBlockLength));
								
			length__ = Convert.ToUInt64(LastBlockLength_Bi.ToString());
		}

		int dataLength = src.Length;								//get length of src.

		MemoryStream fin 	=	new MemoryStream(src);
		MemoryStream fout	=	new MemoryStream();
                                
		try
		{
			LoadKeyFile(key, UseBigInteger);			//extract public key from "key"-file with xml.

			int n_bitlength = 0;
			if(UseBigInteger == false){
				n_bitlength = rsa.KeySize;													//then, get n_bitlength of modulus from RSA-key.
			}
			else{
				//n_bitlength = n_value.dataLength * 32;
				n_bitlength = bitLength(n_value);
			}

			set_lengths(n_bitlength, UseBigInteger);


			byte[] buffer = new byte[block_size];
			byte[] decbuffer = new byte[block_length];

			BigInteger de, n;
			if(UseBigInteger == false)
			{
				de = (
					(byPub == true)
						?	new BigInteger	(pa_Pub.Exponent)
						:	new BigInteger	(pa_Priv.D)
				);				//extract secret exponent, and convert to BigInteger.
				n = (
					new BigInteger	(
						(
							(byPub == true)
								? pa_Pub
								: pa_Priv
						).Modulus
					)
				);			//extract modulus and confert to BigInteger.
			}
			else{
				de	=	( (byPub == true) ? e_value : d_value);
				n	=	n_value;
			}
								
			int max_blocks = (int)(src.Length / block_size);
			int current_block = 0;
			
			int c = 0;
								
			bool	isNextUlong = false;
			while ((c = fin.Read(buffer, 0, block_size)) > 0)  //читать файл блоками по block_size
			{

//				log("dec: buffer: "+BitConverter.ToString(buffer).Replace("-", string.Empty)+" "+buffer.Length);

				decbuffer = DecryptFullBlockOrLastBlock(
					ref rsa
				,	ref buffer
				,	ref block_size
				,	ref c
				,	ref isNextUlong
				,	UseBigInteger
				,	dataLength
				,	de
				,	n
				,	current_block
				,	max_blocks
				,	length__
				,	!byPub
				);

				if(UseBigInteger == true && isNextUlong == true){
					break;
				}
				
				fout.Write(decbuffer, 0, decbuffer.Length); //write this later.
				current_block += 1;

//				log("dec: decbuffer: "+BitConverter.ToString(decbuffer).Replace("-", string.Empty)+" "+decbuffer.Length);

			}
			fin.Close();
			dest = fout.ToArray();
			fout.Close();
		}
		catch (ArgumentException)// e)// when (e.ParamName == "…")
		{
			fin.Close();
			dest = fout.ToArray();
			fout.Close();
			//log(e + ", "+e.ParamName);
		}
		catch (Exception ex)
		{
			fin.Close();
			dest = fout.ToArray();
			fout.Close();
			log("ex: "+ex.ToString());
		}
	}

	//return "dest"-bytearray
	public static	byte[]	DecryptBytes(
		string key
	,	byte[] src
	,	bool UseBigInteger = false
	,	bool byPub = false
	)
	{
		byte[] dest = new byte[0];

		try{
			DecryptBytes(
				key
			,	ref src
			,	ref dest
			,	UseBigInteger
			,	byPub
			);
		}
		catch(Exception ex){
			log("ex: "+ex.ToString());
		}
		return dest;
	}
	//--------------------END RSABigInteger.--------------------

}

public static class RsaExtensions
{
//
//	The following extensions for RSACryptoServiceProvider, allow to encrypt data by priv, and decrypt by pub, without UseBigIngeter = true; 
//
//	RSACryptoServiceProvider.Encrypt()		can encrypt only by pub.
//	RSACryptoServiceProvider.Decrypt()		can decrypt only by priv.
//	encryption by priv, and decryption by pub - is not supported.
//		rsa.Decrypt() can not find priv to decrypt, when trying to decrypt by pub.
//	Encryption by priv, and decryption by pub - this is signing and verify RSA-operations.
//	But, using RSACryptoServiceProvider's methods, this working with hash of data, not with data.
//	Signing, and verify digital RSA signature, have the following scheme:
//		s = m ^ d mod n;		-	(compute signature):	"encrypt" by priv "(d, n)" the message "m", into sinature "s"
//		send (m, s)
//		m_ = s ^ e mod n;		-	(extract message):		"decrypt" by pub (e, n) the signature s, into message m_
//		compare m and m_		-	(verify signature):		"compare" an existing "m", and "m_".
//		
//	//Usage:
//	//	BigInteger.LoadKeyFile("privateKeyXmlFile.txt");										//load privkey to (rsa, pa_Priv, pa_pub)-values, or BigIntegers.
//	//	byte[] encryptByPriv = (BigInteger.rsa).EncryptByPrivateKey(sourceBytes);				//return bytes
//	//	byte[] decryptByPub = (BigInteger.rsa).DecryptByPublicKey(encryptByPriv);				//return bytes
//	//	log("CompareBytes: "+BigInteger.CompareBytes(decryptByPub, sourceBytes));	//must to be true.
//		
//

	//Usage: byte[] EncryptedBytes = (BigInteger.rsa).EncryptByPrivateKey(sourceBytes); //return EncryptedBytes
	public static byte[] EncryptByPrivateKey(
		this RSACryptoServiceProvider rsaWithPriv
	,	byte[] data
	,	string key = ""
	)
	{
		if (data == null){
			throw new ArgumentNullException("data");
		}
		if (
				(
						( key == "" )
					&&	(rsaWithPriv.PublicOnly)
				)
				||
				(
						(key != "")
					&&	(!key.Contains("<D>"))
				)
		){
			throw new InvalidOperationException("Private key is not loaded");
		}
		byte[] encryptBytesByBigIntegerPriv = 	BigInteger.EncryptBytes(
																		(
																			(key != "")
																			? key
																			: rsaWithPriv.ToXmlString(true)
																		),
																		data, true, true
												)
		;
		return encryptBytesByBigIntegerPriv;
	}

	//Usage: byte[] DecryptedBytes = (BigInteger.rsa).DecryptByPublicKey(sourceBytes); //return DecryptedBytes
	public static byte[] DecryptByPublicKey(
		this RSACryptoServiceProvider rsaWithPrivPub
	,	byte[] cipherData
	,	string key = ""
	)
	{
		if (cipherData == null){
			throw new ArgumentNullException("cipherData");
		}

		byte[] decryptBytesByBigIntegerPub = new byte[0];
		try{
			decryptBytesByBigIntegerPub = BigInteger
				.DecryptBytes
				(
					(
						(key != "")
							? key
							:	rsaWithPrivPub.ToXmlString(true)	//rsa with priv
					)
				,	cipherData								//decrypt
				,	true									//UseBigInteger
				,	true									//byPub
				)
			;
		}
		catch(Exception ex){
			Console.WriteLine("ex: "+ex.ToString());
		}
		return decryptBytesByBigIntegerPub;
	}
}	//end extended RSA-methods to encrypt by priv, and decrypt by pub (sign and restore the message from signature, to verify this signature).
