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

#ifndef NO_MUTEX_H
#define NO_MUTEX_H

namespace std {
    struct mutex {
        void lock() {}
        void unlock() {}
    };

    static const bool memory_order_relaxed = true;
    static const bool memory_order_acquire = true;

    inline void atomic_thread_fence(bool)
    {}

    template<class T>
    struct atomic {
        atomic()
        {}

        atomic(bool _val) :
        val(_val)
        {}

        void store(bool _val, bool) {
            val = _val;
        }
        bool load(bool) const {
            return val;
        }
        operator bool() {
            return val;
        }
        T val;
    };
}

#endif //NO_MUTEX_H
