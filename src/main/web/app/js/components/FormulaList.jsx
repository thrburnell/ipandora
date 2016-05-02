import React from 'react'
import Formula from './Formula'

const FormulaList = ({ formulas }) => (
  <div>
    { formulas.map((formula, i) =>
      <Formula
        key={i}
        {...formula}
      />
    )}
  </div>
)

export default FormulaList

