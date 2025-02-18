/*
 * Copyright (c) 2018 Demerzel Solutions Limited
 * This file is part of the Nethermind library.
 *
 * The Nethermind library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The Nethermind library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the Nethermind. If not, see <http://www.gnu.org/licenses/>.
 */
using System; 
using System.IO; // 引入 System.IO 命名空间
using System.Linq;
using Nethermind.Core.Specs;

namespace Nethermind.Evm
{
    public static class CodeDepositHandler
    {
        public static long CalculateCost(int byteCodeLength, IReleaseSpec spec)
        {
            //  using (StreamWriter writer = new StreamWriter("evm_log.txt", true)) // true 表示追加模式
            // {
            //     string logMessage =  $"spec.IsEip170Enabled && byteCodeLength > spec.MaxCodeSize {spec.IsEip170Enabled} {byteCodeLength} {spec.MaxCodeSize}" +"\n";
            //     writer.WriteLine(logMessage);
            // }
            if (spec.IsEip170Enabled && byteCodeLength > spec.MaxCodeSize)
            { 
                return long.MaxValue;
            }

            return GasCostOf.CodeDeposit * byteCodeLength;
        }
    }
}