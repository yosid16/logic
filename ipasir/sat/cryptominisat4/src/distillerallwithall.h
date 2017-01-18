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

#ifndef __DISTILLERALL_WITH_ALL_H__
#define __DISTILLERALL_WITH_ALL_H__

#include <vector>
#include "clause.h"
#include "constants.h"
#include "solvertypes.h"
#include "cloffset.h"
#include "watcharray.h"

namespace CMSat {

using std::vector;

class Solver;
class Clause;

class DistillerAllWithAll {
    public:
        DistillerAllWithAll(Solver* solver);
        bool distill(uint32_t queueByBy = 2);

        struct Stats
        {
            void clear()
            {
                Stats tmp;
                *this = tmp;
            }

            Stats& operator+=(const Stats& other);
            void print_short(const Solver* solver) const;
            void print(const size_t nVars) const;

            double time_used = 0.0;
            uint64_t timeOut = 0;
            uint64_t zeroDepthAssigns = 0;
            uint64_t numClShorten = 0;
            uint64_t numLitsRem = 0;
            uint64_t checkedClauses = 0;
            uint64_t potentialClauses = 0;
            uint64_t numCalled = 0;
        };

        const Stats& get_stats() const;

    private:

        ClOffset try_distill_clause_and_return_new(
            ClOffset offset
            , const bool red
            , const ClauseStats* stats
            , const uint32_t queueByBy
        );

        //Actual algorithms used
        bool distill_long_irred_cls(uint32_t queueByBy);
        bool distill_tri_irred_cls();
        Solver* solver;

        //For distill
        vector<Lit> lits;
        vector<Lit> uselessLits;
        uint64_t extraTime;

        //Global status
        Stats runStats;
        Stats globalStats;
        size_t numCalls = 0;

};

inline const DistillerAllWithAll::Stats& DistillerAllWithAll::get_stats() const
{
    return globalStats;
}

} //end namespace

#endif //__DISTILLERALL_WITH_ALL_H__
