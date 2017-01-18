/*
 * CryptoMiniSat
 *
 * Copyright (c) 2009-2015, Mate Soos. All rights reserved.
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation
 * version 2.0 of the License.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with this library; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston,
 * MA 02110-1301  USA
*/

#ifndef MATRIXFINDER_H
#define MATRIXFINDER_H

#include <vector>
#include <map>
#include "xor.h"
#include "constants.h"

namespace CMSat {

class Solver;

using std::map;
using std::vector;
using std::pair;

class MatrixFinder {

    public:
        MatrixFinder(Solver* solver);
        bool findMatrixes();

    private:
        uint32_t setMatrixes();

        struct mysorter
        {
            bool operator () (const pair<uint32_t, uint32_t>& left, const pair<uint32_t, uint32_t>& right)
            {
                return left.second < right.second;
            }
        };

        inline uint32_t fingerprint(const Xor& c) const;
        inline bool firstPartOfSecond(const Xor& c1, const Xor& c2) const;

        map<uint32_t, vector<uint32_t> > reverseTable; //matrix -> vars
        vector<uint32_t> table; //var -> matrix
        uint32_t matrix_no;

        Solver* solver;
};

}

#endif //MATRIXFINDER_H
